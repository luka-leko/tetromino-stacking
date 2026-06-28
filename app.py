"""
Tetromino Stacking — drag, rotate, and place the 7 tetrominoes on a 20×10 grid.

Controls:
  Drag a piece from the palette onto the grid.
  Click and drag a placed piece to pick it up and move it.
  Press [R] while dragging to rotate 90° clockwise.
  Click "Clear Grid" to reset the board.
"""

import tkinter as tk
import copy
import json
import os
from tkinter import filedialog, messagebox

# ── Constants ────────────────────────────────────────────────────────────────

CELL_SIZE = 32  # pixels per grid cell
GRID_COLS = 10
GRID_ROWS = 20
MINI_CELL = 22  # pixels per cell in the palette previews
PALETTE_BOX = 4  # palette preview is PALETTE_BOX × PALETTE_BOX cells

COLORS = {
    "I": "#00C8C8",
    "O": "#C8B400",
    "T": "#9600C8",
    "S": "#00A000",
    "Z": "#C82000",
    "J": "#2850C8",
    "L": "#C86000",
}

# Shapes encoded as row-major 0/1 grids
TETROMINOES = {
    "I": [[1, 1, 1, 1]],
    "O": [[1, 1], [1, 1]],
    "T": [[0, 1, 0], [1, 1, 1]],
    "S": [[0, 1, 1], [1, 1, 0]],
    "Z": [[1, 1, 0], [0, 1, 1]],
    "J": [[1, 0, 0], [1, 1, 1]],
    "L": [[0, 0, 1], [1, 1, 1]],
}

PIECE_ORDER = ["I", "O", "T", "S", "Z", "J", "L"]

# Stock limits (how many of each piece the player may use in total)
PIECE_STOCK = {"I": 7, "O": 7, "T": 8, "S": 7, "Z": 7, "J": 7, "L": 7}

# Reverse lookup: colour → piece name
COLOR_TO_NAME = {v: k for k, v in COLORS.items()}

# ── Helpers ──────────────────────────────────────────────────────────────────


def rotate_cw(shape):
    """Return a new shape rotated 90° clockwise."""
    return [list(row) for row in zip(*shape[::-1])]


def shape_dims(shape):
    rows = len(shape)
    cols = max(len(r) for r in shape)
    return rows, cols


def rotate_cells_cw(cells, rows, cols):
    """Rotate relative cell tuples (r, c, color, piece_id) 90° clockwise."""
    return [(c, rows - 1 - r, color, piece_id) for r, c, color, piece_id in cells]


# ── Application ───────────────────────────────────────────────────────────────


class TetrominoApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("Tetromino Stacking")
        self.root.configure(bg="#12121e")
        self.root.resizable(False, False)
        try:
            # Works on Windows; may fail on some Linux/WSL window managers.
            self.root.state("zoomed")
        except tk.TclError:
            try:
                # Supported by some X11/Wayland environments.
                self.root.attributes("-zoomed", True)
            except tk.TclError:
                # Keep a normal window on environments without zoom support.
                self.root.geometry("1366x900")
        self.root.update()  # Force update to get actual screen dimensions

        # Calculate dynamic CELL_SIZE based on screen dimensions
        screen_width = self.root.winfo_width()
        screen_height = self.root.winfo_height()

        # Account for palette (~220px), padding, and margins
        available_width = screen_width - 260  # width minus palette sidebar
        available_height = screen_height - 160  # height minus title bar, buttons, trash

        cell_size_h = available_height // GRID_ROWS
        cell_size_w = available_width // GRID_COLS
        self.CELL_SIZE = min(cell_size_h, cell_size_w, 48)  # Cap at 48px
        self.MINI_CELL = max(
            16, (self.CELL_SIZE * 22) // 32
        )  # Scale mini cell proportionally

        self.root.focus_force()

        # 2-D board: None or a colour string per cell
        self.grid: list[list] = [[None] * GRID_COLS for _ in range(GRID_ROWS)]
        # Parallel board storing a unique tetromino ID per occupied cell
        self.grid_ids: list[list] = [[None] * GRID_COLS for _ in range(GRID_ROWS)]
        self.next_piece_id = 1
        # Lock groups: piece_id -> group_id
        self.piece_group: dict[int, int] = {}
        self.next_group_id = 1
        self.selected_piece_ids: set[int] = set()

        # Piece stock counters
        self.stock: dict[str, int] = dict(PIECE_STOCK)

        # Palette widget refs for updating counter labels / dimming
        self._pal_canvas: dict[str, tk.Canvas] = {}
        self._pal_label: dict[str, tk.Label] = {}

        # Active drag state
        self.drag_piece: dict | None = None  # {name, cells, piece_ids}
        self.drag_win: tk.Toplevel | None = None
        self._drag_lifted_cells: list[tuple[int, int, str, int]] = (
            []
        )  # original positions if lifted from grid
        self._grid_press_pos: tuple | None = None  # (col, row, x_root, y_root)
        self._grid_press_piece_id: int | None = None
        self._grid_press_ctrl: bool = False
        self._last_ghost_pos: tuple[int, int] | None = None
        self._last_trash_hover: bool = False
        self._last_drag_root_pos: tuple[int, int] | None = None
        self._pending_drag_xy: tuple[int, int] | None = None
        self._drag_update_queued: bool = False

        # Undo stack: list of snapshots
        self.undo_stack: list[dict] = []

        self._build_ui()

        # Key bindings (focused on root)
        self.root.bind("<KeyPress-r>", self._on_key_rotate)
        self.root.bind("<KeyPress-R>", self._on_key_rotate)
        self.root.bind("<Button-3>", self._on_right_click_rotate)
        self.root.bind("<Control-c>", self._on_copy)
        self.root.bind("<Control-z>", self._on_undo)
        self.root.bind("<Delete>", self._on_delete_selected)

    # ── UI construction ──────────────────────────────────────────────────────

    def _build_ui(self):
        # ── Left palette ────────────────────────────────────────────────────
        pal = tk.Frame(self.root, bg="#1a1a30", padx=14, pady=14)
        pal.pack(side=tk.LEFT, fill=tk.Y)

        tk.Label(
            pal,
            text="PIECES",
            bg="#1a1a30",
            fg="#e94560",
            font=("Consolas", 11, "bold"),
        ).pack(pady=(0, 10))

        for name in PIECE_ORDER:
            self._add_palette_piece(pal, name)

        # ── Right grid area ──────────────────────────────────────────────────
        right = tk.Frame(self.root, bg="#12121e", padx=14, pady=14)
        right.pack(side=tk.LEFT)

        tk.Label(
            right,
            text="10 × 20  GRID",
            bg="#12121e",
            fg="#e94560",
            font=("Consolas", 11, "bold"),
        ).pack(pady=(0, 8))

        self.grid_canvas = tk.Canvas(
            right,
            width=GRID_COLS * self.CELL_SIZE,
            height=GRID_ROWS * self.CELL_SIZE,
            bg="#080810",
            highlightthickness=2,
            highlightbackground="#2a2a4a",
        )
        self.grid_canvas.pack()
        self._redraw_grid()

        # Allow picking up placed pieces directly from the grid
        self.grid_canvas.bind("<ButtonPress-1>", self._start_grid_drag)
        self.grid_canvas.bind("<B1-Motion>", self._on_drag_motion)
        self.grid_canvas.bind("<ButtonRelease-1>", self._on_drag_release)

        # ── Buttons panel (right of grid) ─────────────────────────────────
        btn_panel = tk.Frame(self.root, bg="#12121e", padx=10, pady=14)
        btn_panel.pack(side=tk.LEFT, anchor="n")

        def _make_btn(parent, text, command, bg, active_bg):
            tk.Button(
                parent,
                text=text,
                command=command,
                bg=bg,
                fg="white",
                font=("Consolas", 10, "bold"),
                relief=tk.FLAT,
                padx=10,
                pady=8,
                cursor="hand2",
                width=14,
                activebackground=active_bg,
                activeforeground="white",
            ).pack(fill=tk.X, pady=4)

        # Group 1: board editing / deletion
        _make_btn(btn_panel, "Clear Grid", self._clear_grid, "#e94560", "#b83048")
        _make_btn(
            btn_panel, "Group Selected", self._lock_selected, "#b08400", "#8a6500"
        )
        _make_btn(
            btn_panel, "Un-Group Selected", self._unlock_selected, "#c86000", "#a04800"
        )

        self.trash_canvas = tk.Canvas(
            btn_panel,
            width=GRID_COLS * self.CELL_SIZE,
            height=56,
            bg="#1a0a0a",
            highlightthickness=2,
            highlightbackground="#4a1a1a",
            cursor="X_cursor",
        )
        self.trash_canvas.pack(fill=tk.X, pady=(6, 6))
        self._draw_trash(hovering=False)

        # Group 2: file operations
        tk.Label(btn_panel, text="──────────", bg="#12121e", fg="#2a2a44").pack(
            pady=(2, 4)
        )
        _make_btn(btn_panel, "Save Board", self._save_board, "#2850c8", "#1a3a90")
        _make_btn(btn_panel, "Load Board", self._load_board, "#00a000", "#007000")
        _make_btn(
            btn_panel, "Export to SVG", self._export_grid_image, "#444488", "#303066"
        )

        # ── Controls help ─────────────────────────────────────────────────
        tk.Label(btn_panel, text="──────────", bg="#12121e", fg="#2a2a44").pack(
            pady=(6, 4)
        )

        for hint in (
            "[R] / RClick  Rotate",
            "Drag → place",
            "Click → select",
            "Ctrl+C → hold duplicate",
            "Ctrl+Z → undo",
            "Delete → delete selected",
        ):
            tk.Label(
                btn_panel,
                text=hint,
                bg="#12121e",
                fg="#606080",
                font=("Consolas", 9),
                anchor="w",
            ).pack(fill=tk.X, padx=4)

    def _add_palette_piece(self, parent, name: str):
        color = COLORS[name]
        shape = TETROMINOES[name]
        box = PALETTE_BOX * self.MINI_CELL

        row_frame = tk.Frame(parent, bg="#1a1a30", pady=4)
        row_frame.pack(fill=tk.X)

        tk.Label(
            row_frame,
            text=f" {name} ",
            bg="#1a1a30",
            fg="#8888aa",
            font=("Consolas", 9, "bold"),
            width=3,
        ).pack(side=tk.LEFT)

        canvas = tk.Canvas(
            row_frame,
            width=box,
            height=box,
            bg="#0e0e22",
            highlightthickness=1,
            highlightbackground="#2a2a44",
            cursor="fleur",
        )
        canvas.pack(side=tk.LEFT)

        self._draw_mini(canvas, shape, color)
        self._pal_canvas[name] = canvas

        count_lbl = tk.Label(
            row_frame,
            text=str(self.stock[name]),
            bg="#1a1a30",
            fg="#c8c8e0",
            font=("Consolas", 10, "bold"),
            width=3,
        )
        count_lbl.pack(side=tk.LEFT, padx=(6, 0))
        self._pal_label[name] = count_lbl

        canvas.bind("<ButtonPress-1>", lambda e, n=name: self._start_drag(e, n))
        canvas.bind("<B1-Motion>", self._on_drag_motion)
        canvas.bind("<ButtonRelease-1>", self._on_drag_release)

    # ── Drawing ──────────────────────────────────────────────────────────────

    def _draw_trash(self, hovering: bool):
        self.trash_canvas.delete("all")
        bg = "#3a0a0a" if hovering else "#1a0a0a"
        fg = "#ff6060" if hovering else "#884040"
        self.trash_canvas.configure(bg=bg)
        w = self.trash_canvas.winfo_reqwidth()
        h = self.trash_canvas.winfo_reqheight()
        self.trash_canvas.create_text(
            w // 2, h // 2 - 8, text="🗑", font=("Segoe UI Emoji", 18), fill=fg
        )
        self.trash_canvas.create_text(
            w // 2,
            h // 2 + 14,
            text="DROP TO DELETE",
            font=("Consolas", 8, "bold"),
            fill=fg,
        )

    def _is_over_trash(self, x_root: int, y_root: int) -> bool:
        tx = self.trash_canvas.winfo_rootx()
        ty = self.trash_canvas.winfo_rooty()
        return (
            tx <= x_root <= tx + self.trash_canvas.winfo_width()
            and ty <= y_root <= ty + self.trash_canvas.winfo_height()
        )

    def _draw_mini(self, canvas: tk.Canvas, shape, color: str):
        canvas.delete("all")
        rows_n, cols_n = shape_dims(shape)
        off_r = (PALETTE_BOX - rows_n) // 2
        off_c = (PALETTE_BOX - cols_n) // 2
        m = self.MINI_CELL
        for r, row in enumerate(shape):
            for c, val in enumerate(row):
                if val:
                    x1 = (off_c + c) * m
                    y1 = (off_r + r) * m
                    canvas.create_rectangle(
                        x1 + 2,
                        y1 + 2,
                        x1 + m - 2,
                        y1 + m - 2,
                        fill=color,
                        outline="#3a3a5a",
                        width=1,
                    )

    def _redraw_grid(self):
        self.grid_canvas.delete("all")

        # Grid lines
        w = GRID_COLS * self.CELL_SIZE
        h = GRID_ROWS * self.CELL_SIZE
        for c in range(GRID_COLS + 1):
            x = c * self.CELL_SIZE
            self.grid_canvas.create_line(x, 0, x, h, fill="#14142a", width=1)
        for r in range(GRID_ROWS + 1):
            y = r * self.CELL_SIZE
            self.grid_canvas.create_line(0, y, w, y, fill="#14142a", width=1)

        # Placed cells
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                color = self.grid[r][c]
                if color:
                    self._draw_cell(c, r, color, tags=())

        # Lock group highlights (draw only the outer boundary of each group)
        group_cells: dict[int, set[tuple[int, int]]] = {}
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                piece_id = self.grid_ids[r][c]
                if piece_id is not None:
                    group_id = self.piece_group.get(piece_id)
                    if group_id is not None:
                        group_cells.setdefault(group_id, set()).add((r, c))

        for cells in group_cells.values():
            for r, c in cells:
                x1 = c * self.CELL_SIZE
                y1 = r * self.CELL_SIZE
                x2 = x1 + self.CELL_SIZE
                y2 = y1 + self.CELL_SIZE

                # Top edge
                if (r - 1, c) not in cells:
                    self.grid_canvas.create_line(
                        x1 + 1, y1 + 1, x2 - 1, y1 + 1, fill="#ffffff", width=2
                    )
                # Bottom edge
                if (r + 1, c) not in cells:
                    self.grid_canvas.create_line(
                        x1 + 1, y2 - 1, x2 - 1, y2 - 1, fill="#ffffff", width=2
                    )
                # Left edge
                if (r, c - 1) not in cells:
                    self.grid_canvas.create_line(
                        x1 + 1, y1 + 1, x1 + 1, y2 - 1, fill="#ffffff", width=2
                    )
                # Right edge
                if (r, c + 1) not in cells:
                    self.grid_canvas.create_line(
                        x2 - 1, y1 + 1, x2 - 1, y2 - 1, fill="#ffffff", width=2
                    )

        # Selection highlights
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                piece_id = self.grid_ids[r][c]
                if piece_id in self.selected_piece_ids:
                    x1, y1 = c * self.CELL_SIZE, r * self.CELL_SIZE
                    x2, y2 = x1 + self.CELL_SIZE, y1 + self.CELL_SIZE
                    self.grid_canvas.create_rectangle(
                        x1 + 2,
                        y1 + 2,
                        x2 - 2,
                        y2 - 2,
                        outline="#ffd24a",
                        width=2,
                    )

    def _draw_cell(self, col: int, row: int, color: str, tags=()):
        x1, y1 = col * self.CELL_SIZE, row * self.CELL_SIZE
        x2, y2 = x1 + self.CELL_SIZE, y1 + self.CELL_SIZE
        self.grid_canvas.create_rectangle(
            x1 + 1,
            y1 + 1,
            x2 - 1,
            y2 - 1,
            fill=color,
            outline="#3a3a5a",
            width=1,
            tags=tags,
        )

    def _draw_ghost(self, col: int, row: int):
        self.grid_canvas.delete("ghost")
        cells = self.drag_piece["cells"]
        valid = self._can_place_cells(cells, col, row)

        for r, c, color, _ in cells:
            gc, gr = col + c, row + r
            if 0 <= gc < GRID_COLS and 0 <= gr < GRID_ROWS:
                x1, y1 = gc * self.CELL_SIZE, gr * self.CELL_SIZE
                x2, y2 = x1 + self.CELL_SIZE, y1 + self.CELL_SIZE
                fill = color if valid else "#883030"
                self.grid_canvas.create_rectangle(
                    x1 + 1,
                    y1 + 1,
                    x2 - 1,
                    y2 - 1,
                    fill=fill,
                    outline="white",
                    width=1,
                    stipple="gray50",
                    tags="ghost",
                )

    # ── Drag helpers ─────────────────────────────────────────────────────────

    def _cells_bounds(self, cells) -> tuple[int, int]:
        max_r = max(r for r, _, _, _ in cells)
        max_c = max(c for _, c, _, _ in cells)
        return max_r + 1, max_c + 1

    def _can_place_cells(self, cells, col: int, row: int) -> bool:
        for r, c, _, _ in cells:
            gc, gr = col + c, row + r
            if not (0 <= gc < GRID_COLS and 0 <= gr < GRID_ROWS):
                return False
            if self.grid[gr][gc] is not None:
                return False
        return True

    def _build_cells_from_shape(self, shape, color: str, piece_id):
        cells = []
        for r, row_data in enumerate(shape):
            for c, val in enumerate(row_data):
                if val:
                    cells.append((r, c, color, piece_id))
        return cells

    def _is_over_grid(self, x_root: int, y_root: int) -> bool:
        gx = self.grid_canvas.winfo_rootx()
        gy = self.grid_canvas.winfo_rooty()
        return (
            gx <= x_root <= gx + GRID_COLS * self.CELL_SIZE
            and gy <= y_root <= gy + GRID_ROWS * self.CELL_SIZE
        )

    def _snap_pos(self, x_root: int, y_root: int) -> tuple[int, int]:
        """Return (col, row) for the top-left of the dragged piece, snapped to grid."""
        cells = self.drag_piece["cells"]
        rows_n, cols_n = self._cells_bounds(cells)
        gx = self.grid_canvas.winfo_rootx()
        gy = self.grid_canvas.winfo_rooty()
        lx = x_root - gx - (cols_n * self.CELL_SIZE) // 2
        ly = y_root - gy - (rows_n * self.CELL_SIZE) // 2
        return round(lx / self.CELL_SIZE), round(ly / self.CELL_SIZE)

    def _create_drag_window(self, x_root: int, y_root: int):
        """Create (or recreate) the floating semi-transparent drag preview."""
        if self.drag_win:
            self.drag_win.destroy()
            self.drag_win = None
        if not self.drag_piece:
            return

        cells = self.drag_piece["cells"]
        rows_n, cols_n = self._cells_bounds(cells)
        w, h = cols_n * self.CELL_SIZE, rows_n * self.CELL_SIZE
        ox, oy = w // 2, h // 2

        win = tk.Toplevel(self.root)
        win.overrideredirect(True)
        win.attributes("-topmost", True)
        win.attributes("-alpha", 0.78)
        win.geometry(f"{w}x{h}+{x_root - ox}+{y_root - oy}")
        self._last_drag_root_pos = (x_root, y_root)

        cv = tk.Canvas(win, width=w, height=h, bg="black", highlightthickness=0)
        cv.pack()

        # Let the floating preview handle motion/release so copied "held" pieces
        # can be moved and dropped naturally.
        win.bind("<Motion>", self._on_drag_motion)
        win.bind("<ButtonRelease-1>", self._on_drag_release)
        cv.bind("<ButtonRelease-1>", self._on_drag_release)

        for r, c, color, _ in cells:
            x1, y1 = c * self.CELL_SIZE, r * self.CELL_SIZE
            x2, y2 = x1 + self.CELL_SIZE, y1 + self.CELL_SIZE
            cv.create_rectangle(
                x1 + 1,
                y1 + 1,
                x2 - 1,
                y2 - 1,
                fill=color,
                outline="white",
                width=1,
            )

        # Make the black background transparent on Windows
        try:
            win.wm_attributes("-transparentcolor", "black")
        except Exception:
            pass

        self.drag_win = win

    def _move_drag_window(self, x_root: int, y_root: int):
        if not self.drag_win or not self.drag_piece:
            return
        if self._last_drag_root_pos == (x_root, y_root):
            return
        self._last_drag_root_pos = (x_root, y_root)
        cells = self.drag_piece["cells"]
        rows_n, cols_n = self._cells_bounds(cells)
        ox = (cols_n * self.CELL_SIZE) // 2
        oy = (rows_n * self.CELL_SIZE) // 2
        self.drag_win.geometry(f"+{x_root - ox}+{y_root - oy}")

    # ── Event handlers ───────────────────────────────────────────────────────

    def _start_drag(self, event: tk.Event, name: str):
        if self.stock[name] <= 0:
            return  # no pieces left
        self._push_undo()
        self.stock[name] -= 1
        self._refresh_palette(name)
        cells = self._build_cells_from_shape(TETROMINOES[name], COLORS[name], None)
        self.drag_piece = {
            "name": name,
            "cells": copy.deepcopy(cells),
            "piece_ids": set(),
            "stock_costs": {name: 1},
            "copy_group_by_key": {},
        }
        self._drag_lifted_cells = []
        self._last_ghost_pos = None
        self._last_trash_hover = False
        self._create_drag_window(event.x_root, event.y_root)

    def _start_grid_drag(self, event: tk.Event):
        """Record grid position on button press. Dragging starts on motion."""
        col = event.x // self.CELL_SIZE
        row = event.y // self.CELL_SIZE
        if not (0 <= col < GRID_COLS and 0 <= row < GRID_ROWS):
            self._grid_press_pos = None
            self._grid_press_piece_id = None
            self._grid_press_ctrl = False
            return

        piece_id = self.grid_ids[row][col]
        if piece_id is None:
            self._grid_press_pos = None
            self._grid_press_piece_id = None
            self._grid_press_ctrl = False
            return

        # Record for potential drag or click
        self._grid_press_pos = (col, row, event.x_root, event.y_root)
        self._grid_press_piece_id = piece_id
        self._grid_press_ctrl = bool(event.state & 0x0004)

    def _initiate_grid_drag(self, piece_id: int, event: tk.Event):
        """Actually start dragging the piece from the grid."""
        piece_ids = {piece_id}
        if len(self.selected_piece_ids) > 1 and piece_id in self.selected_piece_ids:
            # If dragging starts on a selected piece, move the full selection together.
            piece_ids = set(self.selected_piece_ids)
        else:
            group_id = self.piece_group.get(piece_id)
            if group_id is not None:
                piece_ids = {
                    pid for pid, gid in self.piece_group.items() if gid == group_id
                }

        # Collect all cells that belong to the dragged piece(s)
        lifted = []
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                pid = self.grid_ids[r][c]
                if pid in piece_ids:
                    lifted.append((r, c, self.grid[r][c], pid))
        if not lifted:
            return

        self._push_undo()

        # Remove them from the grid temporarily
        for r, c, _, _ in lifted:
            self.grid[r][c] = None
            self.grid_ids[r][c] = None
        self._drag_lifted_cells = lifted
        self._redraw_grid()

        # Build a minimal bounding-box relative cell list
        min_r = min(r for r, _, _, _ in lifted)
        min_c = min(c for _, c, _, _ in lifted)
        cells = []
        color = None
        for r, c, clr, pid in lifted:
            cells.append((r - min_r, c - min_c, clr, pid))
            if color is None:
                color = clr

        self.drag_piece = {
            "name": COLOR_TO_NAME.get(color, ""),
            "cells": cells,
            "piece_ids": piece_ids,
            "stock_costs": {},
            "copy_group_by_key": {},
        }
        self._last_ghost_pos = None
        self._last_trash_hover = False
        self._create_drag_window(event.x_root, event.y_root)

    def _on_drag_motion(self, event: tk.Event):
        if (
            not self.drag_piece
            and self._grid_press_piece_id is not None
            and self._grid_press_pos is not None
        ):
            # Check if we've moved enough to start dragging
            start_col, start_row, start_x_root, start_y_root = self._grid_press_pos
            threshold = self.CELL_SIZE // 3  # Movement threshold
            if (
                abs(event.x_root - start_x_root) > threshold
                or abs(event.y_root - start_y_root) > threshold
            ):
                # Start the drag now
                self._initiate_grid_drag(self._grid_press_piece_id, event)

        if not self.drag_piece:
            return

        self._pending_drag_xy = (event.x_root, event.y_root)
        if self._drag_update_queued:
            return
        self._drag_update_queued = True
        self.root.after_idle(self._flush_drag_motion)

    def _flush_drag_motion(self):
        self._drag_update_queued = False
        if not self.drag_piece or self._pending_drag_xy is None:
            return

        x, y = self._pending_drag_xy
        self._pending_drag_xy = None
        self._move_drag_window(x, y)
        if self._is_over_grid(x, y):
            col, row = self._snap_pos(x, y)
            if self._last_ghost_pos != (col, row):
                self._draw_ghost(col, row)
                self._last_ghost_pos = (col, row)
            if self._last_trash_hover:
                self._draw_trash(hovering=False)
                self._last_trash_hover = False
        elif self._is_over_trash(x, y):
            if self._last_ghost_pos is not None:
                self.grid_canvas.delete("ghost")
                self._last_ghost_pos = None
            if not self._last_trash_hover:
                self._draw_trash(hovering=True)
                self._last_trash_hover = True
        else:
            if self._last_ghost_pos is not None:
                self.grid_canvas.delete("ghost")
                self._last_ghost_pos = None
            if self._last_trash_hover:
                self._draw_trash(hovering=False)
                self._last_trash_hover = False

    def _push_undo(self):
        """Snapshot current mutable state onto the undo stack (max 50 entries)."""
        snapshot = {
            "grid": copy.deepcopy(self.grid),
            "grid_ids": copy.deepcopy(self.grid_ids),
            "next_piece_id": self.next_piece_id,
            "piece_group": dict(self.piece_group),
            "next_group_id": self.next_group_id,
            "stock": dict(self.stock),
        }
        self.undo_stack.append(snapshot)
        if len(self.undo_stack) > 50:
            self.undo_stack.pop(0)

    def _on_undo(self, event=None):
        """Restore the previous state from the undo stack."""
        if not self.undo_stack:
            return
        snapshot = self.undo_stack.pop()
        self.grid = snapshot["grid"]
        self.grid_ids = snapshot["grid_ids"]
        self.next_piece_id = snapshot["next_piece_id"]
        self.piece_group = snapshot["piece_group"]
        self.next_group_id = snapshot["next_group_id"]
        self.stock = snapshot["stock"]
        self.selected_piece_ids.clear()
        for name in PIECE_ORDER:
            self._refresh_palette(name)
        self._redraw_grid()

    def _on_drag_release(self, event: tk.Event):
        if self.drag_piece:
            # Handle drag completion
            x, y = event.x_root, event.y_root
            placed = False

            if self._is_over_trash(x, y):
                # Discard: if lifted from grid, return piece stock for each deleted tetromino
                if self._drag_lifted_cells:
                    deleted_piece_ids = {
                        pid for _, _, _, pid in self._drag_lifted_cells
                    }
                    for pid in deleted_piece_ids:
                        found_color = None
                        for _, _, clr, p in self._drag_lifted_cells:
                            if p == pid:
                                found_color = clr
                                break
                        name = COLOR_TO_NAME.get(found_color, "")
                        if name in self.stock:
                            self.stock[name] += 1
                            self._refresh_palette(name)
                else:
                    # Palette/copy drag dropped on trash: refund reserved stock.
                    stock_costs = self.drag_piece.get("stock_costs", {})
                    for name, amount in stock_costs.items():
                        if name in self.stock:
                            self.stock[name] += amount
                            self._refresh_palette(name)
                placed = True
            elif self._is_over_grid(x, y):
                col, row = self._snap_pos(x, y)
                cells = self.drag_piece["cells"]
                if self._can_place_cells(cells, col, row):
                    generated_ids = {}
                    for r, c, color, piece_id in cells:
                        # New pieces (palette or copied cells) receive fresh IDs on drop.
                        if piece_id is None:
                            key = "palette"
                        elif isinstance(piece_id, int) and piece_id < 0:
                            key = piece_id
                        else:
                            key = None

                        if key is not None:
                            if key not in generated_ids:
                                generated_ids[key] = self.next_piece_id
                                self.next_piece_id += 1
                            piece_id = generated_ids[key]
                        self.grid[row + r][col + c] = color
                        self.grid_ids[row + r][col + c] = piece_id

                    # Rebuild copied lock groups on the newly placed IDs.
                    copy_group_by_key = self.drag_piece.get("copy_group_by_key", {})
                    if copy_group_by_key:
                        regroup: dict[int, list[int]] = {}
                        for key, src_gid in copy_group_by_key.items():
                            new_pid = generated_ids.get(key)
                            if new_pid is not None:
                                regroup.setdefault(src_gid, []).append(new_pid)

                        for new_ids in regroup.values():
                            if len(new_ids) >= 2:
                                new_gid = self.next_group_id
                                self.next_group_id += 1
                                for pid in new_ids:
                                    self.piece_group[pid] = new_gid
                    placed = True

            if not placed:
                if self._drag_lifted_cells:
                    # Restore the piece(s) to where they came from (grid drag)
                    for r, c, color, piece_id in self._drag_lifted_cells:
                        self.grid[r][c] = color
                        self.grid_ids[r][c] = piece_id
                else:
                    # Return reserved stock for palette/copy drags that didn't land.
                    stock_costs = self.drag_piece.get("stock_costs", {})
                    for name, amount in stock_costs.items():
                        if name in self.stock:
                            self.stock[name] += amount
                            self._refresh_palette(name)

            self._drag_lifted_cells = []
            self._redraw_grid()
            self._draw_trash(hovering=False)
            self.grid_canvas.delete("ghost")
            self._last_ghost_pos = None
            self._last_trash_hover = False
            self._last_drag_root_pos = None
            self._pending_drag_xy = None
            self._drag_update_queued = False
            if self.drag_win:
                self.drag_win.destroy()
                self.drag_win = None
            self.drag_piece = None
        elif self._grid_press_piece_id is not None:
            # No drag happened, this was just a click - replace selection
            piece_id = self._grid_press_piece_id
            group_id = self.piece_group.get(piece_id)

            if group_id is not None:
                target_selection = {
                    pid for pid, gid in self.piece_group.items() if gid == group_id
                }
            else:
                target_selection = {piece_id}

            # Ctrl+Left Click toggles clicked tetromino/group in current selection.
            if self._grid_press_ctrl:
                if target_selection.issubset(self.selected_piece_ids):
                    self.selected_piece_ids.difference_update(target_selection)
                else:
                    self.selected_piece_ids.update(target_selection)
            else:
                # Left click selects one tetromino/group and clears prior selection.
                if self.selected_piece_ids == target_selection:
                    self.selected_piece_ids.clear()
                else:
                    self.selected_piece_ids = set(target_selection)
            self._redraw_grid()

        self._grid_press_pos = None
        self._grid_press_piece_id = None
        self._grid_press_ctrl = False

    def _on_key_rotate(self, event: tk.Event):
        if not self.drag_piece:
            return
        cells = self.drag_piece["cells"]
        rows_n, cols_n = self._cells_bounds(cells)
        self.drag_piece["cells"] = rotate_cells_cw(cells, rows_n, cols_n)
        x = self.root.winfo_pointerx()
        y = self.root.winfo_pointery()
        self._create_drag_window(x, y)
        if self._is_over_grid(x, y):
            col, row = self._snap_pos(x, y)
            self._draw_ghost(col, row)

    def _on_right_click_rotate(self, event: tk.Event):
        if not self.drag_piece:
            return
        cells = self.drag_piece["cells"]
        rows_n, cols_n = self._cells_bounds(cells)
        self.drag_piece["cells"] = rotate_cells_cw(cells, rows_n, cols_n)
        x = self.root.winfo_pointerx()
        y = self.root.winfo_pointery()
        self._create_drag_window(x, y)
        if self._is_over_grid(x, y):
            col, row = self._snap_pos(x, y)
            self._draw_ghost(col, row)
        return "break"  # Suppress context menu

    def _lock_selected(self):
        if len(self.selected_piece_ids) < 2:
            messagebox.showinfo(
                "Group Selected", "Select at least 2 tetrominoes with Ctrl+click."
            )
            return
        self._push_undo()
        gid = self.next_group_id
        self.next_group_id += 1
        for pid in self.selected_piece_ids:
            self.piece_group[pid] = gid
        self.selected_piece_ids.clear()
        self._redraw_grid()

    def _unlock_selected(self):
        if not self.selected_piece_ids:
            messagebox.showinfo(
                "Un-Group Selected", "Select at least 1 tetromino to ungroup."
            )
            return
        self._push_undo()
        for pid in self.selected_piece_ids:
            if pid in self.piece_group:
                del self.piece_group[pid]
        self.selected_piece_ids.clear()
        self._redraw_grid()

    def _on_delete_selected(self, event=None):
        """Delete selected tetrominoes from the grid and return their stock."""
        if self.drag_piece or not self.selected_piece_ids:
            return "break"

        # Only delete IDs that currently exist on the grid.
        selected_on_grid = set()
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                pid = self.grid_ids[r][c]
                if pid in self.selected_piece_ids:
                    selected_on_grid.add(pid)

        if not selected_on_grid:
            self.selected_piece_ids.clear()
            self._redraw_grid()
            return "break"

        self._push_undo()

        # Return one stock count per deleted tetromino.
        for pid in selected_on_grid:
            found_color = None
            for r in range(GRID_ROWS):
                for c in range(GRID_COLS):
                    if self.grid_ids[r][c] == pid:
                        found_color = self.grid[r][c]
                        break
                if found_color is not None:
                    break
            if found_color in COLOR_TO_NAME:
                name = COLOR_TO_NAME[found_color]
                self.stock[name] += 1
                self._refresh_palette(name)

        # Remove selected cells and their group mappings.
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                if self.grid_ids[r][c] in selected_on_grid:
                    self.grid[r][c] = None
                    self.grid_ids[r][c] = None

        for pid in selected_on_grid:
            self.piece_group.pop(pid, None)

        self.selected_piece_ids.clear()
        self._redraw_grid()
        return "break"

    def _on_copy(self, event=None):
        """Create a duplicate of selected tetrominoes and hold it for placement."""
        if self.drag_piece or not self.selected_piece_ids:
            return "break"

        # Collect all cells for selected piece IDs.
        selected_cells = []
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                pid = self.grid_ids[r][c]
                if pid in self.selected_piece_ids:
                    selected_cells.append((r, c, self.grid[r][c], pid))

        if not selected_cells:
            return "break"

        # Build per-piece color map and required stock for this copy action.
        piece_colors = {}
        for _, _, color, piece_id in selected_cells:
            if piece_id not in piece_colors:
                piece_colors[piece_id] = color

        stock_costs = {}
        for color in piece_colors.values():
            name = COLOR_TO_NAME.get(color)
            if name is not None:
                stock_costs[name] = stock_costs.get(name, 0) + 1

        missing = []
        for name, amount in stock_costs.items():
            if self.stock[name] < amount:
                missing.append(f"{name}: need {amount}, have {self.stock[name]}")

        if missing:
            messagebox.showinfo(
                "Copy Failed",
                "Not enough tetrominoes in stock for this copy:\n" + "\n".join(missing),
            )
            return "break"

        self._push_undo()
        for name, amount in stock_costs.items():
            self.stock[name] -= amount
            self._refresh_palette(name)

        # Normalize to bounding box and mark copied piece IDs as negative.
        # Negative IDs are remapped to fresh IDs when dropped.
        min_r = min(r for r, _, _, _ in selected_cells)
        min_c = min(c for _, c, _, _ in selected_cells)
        cells = []
        copy_group_by_key = {}
        for r, c, color, piece_id in selected_cells:
            key = -piece_id
            cells.append((r - min_r, c - min_c, color, key))
            src_gid = self.piece_group.get(piece_id)
            if src_gid is not None:
                copy_group_by_key[key] = src_gid

        self.drag_piece = {
            "name": "",
            "cells": cells,
            "piece_ids": set(),
            "stock_costs": stock_costs,
            "copy_group_by_key": copy_group_by_key,
        }
        self._drag_lifted_cells = []
        self._last_ghost_pos = None
        self._last_trash_hover = False

        x = self.root.winfo_pointerx()
        y = self.root.winfo_pointery()
        self._create_drag_window(x, y)
        if self._is_over_grid(x, y):
            col, row = self._snap_pos(x, y)
            self._draw_ghost(col, row)
        return "break"

    def _refresh_palette(self, name: str):
        """Update the counter label and visual state for one palette piece."""
        count = self.stock[name]
        lbl = self._pal_label[name]
        cv = self._pal_canvas[name]
        if count > 0:
            lbl.configure(text=str(count), fg="#c8c8e0")
            cv.configure(highlightbackground="#2a2a44", cursor="fleur")
            self._draw_mini(cv, TETROMINOES[name], COLORS[name])
        else:
            lbl.configure(text="0", fg="#663333")
            cv.configure(highlightbackground="#441a1a", cursor="arrow")
            self._draw_mini_dimmed(cv, TETROMINOES[name])

    def _draw_mini_dimmed(self, canvas: tk.Canvas, shape):
        canvas.delete("all")
        rows_n, cols_n = shape_dims(shape)
        off_r = (PALETTE_BOX - rows_n) // 2
        off_c = (PALETTE_BOX - cols_n) // 2
        m = self.MINI_CELL
        for r, row in enumerate(shape):
            for c, val in enumerate(row):
                if val:
                    x1 = (off_c + c) * m
                    y1 = (off_r + r) * m
                    canvas.create_rectangle(
                        x1 + 2,
                        y1 + 2,
                        x1 + m - 2,
                        y1 + m - 2,
                        fill="#2a2a3a",
                        outline="#1e1e2e",
                        width=1,
                    )

    def _clear_grid(self):
        self._push_undo()
        self.grid = [[None] * GRID_COLS for _ in range(GRID_ROWS)]
        self.grid_ids = [[None] * GRID_COLS for _ in range(GRID_ROWS)]
        self.next_piece_id = 1
        self.piece_group = {}
        self.next_group_id = 1
        self.selected_piece_ids.clear()
        self.stock = dict(PIECE_STOCK)
        for name in PIECE_ORDER:
            self._refresh_palette(name)
        self._redraw_grid()

    def _save_board(self):
        """Save the current board state to a JSON file."""
        file_path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            initialfile="tetromino_board.json",
        )
        if not file_path:
            return

        try:
            board_data = {
                "grid": self.grid,
                "grid_ids": self.grid_ids,
                "stock": self.stock,
                "next_piece_id": self.next_piece_id,
                "piece_group": self.piece_group,
                "next_group_id": self.next_group_id,
            }
            with open(file_path, "w") as f:
                json.dump(board_data, f, indent=2)
        except Exception as e:
            messagebox.showerror("Error", f"Failed to save board:\n{str(e)}")

    def _export_grid_image(self):
        """Export the grid to an SVG file."""
        file_path = filedialog.asksaveasfilename(
            defaultextension=".svg",
            filetypes=[("SVG image", "*.svg")],
            initialfile="tetromino_grid.svg",
        )
        if not file_path:
            return

        if os.path.splitext(file_path)[1].lower() != ".svg":
            file_path = file_path + ".svg"

        w = GRID_COLS * self.CELL_SIZE
        h = GRID_ROWS * self.CELL_SIZE

        lines = [
            '<?xml version="1.0" encoding="UTF-8"?>',
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" viewBox="0 0 {w} {h}">',
            f'<rect x="0" y="0" width="{w}" height="{h}" fill="#080810"/>',
        ]

        # Grid lines
        for c in range(GRID_COLS + 1):
            x = c * self.CELL_SIZE
            lines.append(
                f'<line x1="{x}" y1="0" x2="{x}" y2="{h}" stroke="#14142a" stroke-width="1"/>'
            )
        for r in range(GRID_ROWS + 1):
            y = r * self.CELL_SIZE
            lines.append(
                f'<line x1="0" y1="{y}" x2="{w}" y2="{y}" stroke="#14142a" stroke-width="1"/>'
            )

        # Placed cells
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                color = self.grid[r][c]
                if color:
                    x = c * self.CELL_SIZE + 1
                    y = r * self.CELL_SIZE + 1
                    sz = self.CELL_SIZE - 2
                    lines.append(
                        f'<rect x="{x}" y="{y}" width="{sz}" height="{sz}" fill="{color}" stroke="#3a3a5a" stroke-width="1"/>'
                    )

        # Lock group outlines (outer boundary only)
        group_cells: dict[int, set[tuple[int, int]]] = {}
        for r in range(GRID_ROWS):
            for c in range(GRID_COLS):
                piece_id = self.grid_ids[r][c]
                if piece_id is not None:
                    group_id = self.piece_group.get(piece_id)
                    if group_id is not None:
                        group_cells.setdefault(group_id, set()).add((r, c))

        for cells in group_cells.values():
            for r, c in cells:
                x1 = c * self.CELL_SIZE
                y1 = r * self.CELL_SIZE
                x2 = x1 + self.CELL_SIZE
                y2 = y1 + self.CELL_SIZE

                if (r - 1, c) not in cells:
                    lines.append(
                        f'<line x1="{x1 + 1}" y1="{y1 + 1}" x2="{x2 - 1}" y2="{y1 + 1}" stroke="#ffffff" stroke-width="2"/>'
                    )
                if (r + 1, c) not in cells:
                    lines.append(
                        f'<line x1="{x1 + 1}" y1="{y2 - 1}" x2="{x2 - 1}" y2="{y2 - 1}" stroke="#ffffff" stroke-width="2"/>'
                    )
                if (r, c - 1) not in cells:
                    lines.append(
                        f'<line x1="{x1 + 1}" y1="{y1 + 1}" x2="{x1 + 1}" y2="{y2 - 1}" stroke="#ffffff" stroke-width="2"/>'
                    )
                if (r, c + 1) not in cells:
                    lines.append(
                        f'<line x1="{x2 - 1}" y1="{y1 + 1}" x2="{x2 - 1}" y2="{y2 - 1}" stroke="#ffffff" stroke-width="2"/>'
                    )

        lines.append("</svg>")
        with open(file_path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))

    def _load_board(self):
        """Load a board state from a JSON file."""
        file_path = filedialog.askopenfilename(
            filetypes=[("JSON files", "*.json"), ("All files", "*.*")],
            initialfile="tetromino_board.json",
        )
        if not file_path:
            return

        self._push_undo()

        try:
            with open(file_path, "r") as f:
                board_data = json.load(f)

            # Validate and restore grid
            grid = board_data.get("grid")
            if (
                isinstance(grid, list)
                and len(grid) == GRID_ROWS
                and all(isinstance(row, list) and len(row) == GRID_COLS for row in grid)
            ):
                self.grid = grid
            else:
                raise ValueError("Invalid grid in saved file")

            # Validate and restore piece IDs (required for independent piece movement)
            grid_ids = board_data.get("grid_ids")
            if (
                isinstance(grid_ids, list)
                and len(grid_ids) == GRID_ROWS
                and all(
                    isinstance(row, list) and len(row) == GRID_COLS for row in grid_ids
                )
            ):
                self.grid_ids = grid_ids
            else:
                # Backward compatibility for older save files without grid IDs
                self.grid_ids = [[None] * GRID_COLS for _ in range(GRID_ROWS)]
                next_id = 1
                for r in range(GRID_ROWS):
                    for c in range(GRID_COLS):
                        if self.grid[r][c] is not None:
                            self.grid_ids[r][c] = next_id
                            next_id += 1
                self.next_piece_id = next_id

            # Validate and restore stock
            stock = board_data.get("stock")
            if isinstance(stock, dict) and all(k in stock for k in PIECE_ORDER):
                self.stock = {k: int(stock[k]) for k in PIECE_ORDER}
            else:
                raise ValueError("Invalid stock in saved file")

            if "next_piece_id" in board_data:
                self.next_piece_id = max(int(board_data["next_piece_id"]), 1)
            elif isinstance(grid_ids, list):
                max_id = 0
                for row in self.grid_ids:
                    for pid in row:
                        if isinstance(pid, int) and pid > max_id:
                            max_id = pid
                self.next_piece_id = max_id + 1

            # Restore lock groups
            piece_group = board_data.get("piece_group")
            if isinstance(piece_group, dict):
                cleaned = {}
                for k, v in piece_group.items():
                    try:
                        cleaned[int(k)] = int(v)
                    except Exception:
                        continue
                self.piece_group = cleaned
            else:
                self.piece_group = {}

            if "next_group_id" in board_data:
                self.next_group_id = max(int(board_data["next_group_id"]), 1)
            else:
                max_gid = 0
                for gid in self.piece_group.values():
                    if isinstance(gid, int) and gid > max_gid:
                        max_gid = gid
                self.next_group_id = max_gid + 1
            self.selected_piece_ids.clear()

            # Refresh UI
            for name in PIECE_ORDER:
                self._refresh_palette(name)
            self._redraw_grid()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load board:\n{str(e)}")


# ── Entry point ───────────────────────────────────────────────────────────────

if __name__ == "__main__":
    root = tk.Tk()
    TetrominoApp(root)
    root.mainloop()
