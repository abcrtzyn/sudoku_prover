import threading
from typing import Any, List
import arcade.gui as gui
from pyglet.graphics import Batch
import arcade

from sudoku_prover_ui.proof_engine import ProofEngine
from sudoku_prover_ui.puzzle import Puzzle

NORMAL_STYLE = gui.UIFlatButton.DEFAULT_STYLE

# A highlighted look for the active mode
ACTIVE_STYLE = {
    "normal": gui.UIFlatButton.UIStyle(bg=arcade.color.ARMY_GREEN),
    "hover": gui.UIFlatButton.UIStyle(bg=arcade.color.FIELD_DRAB),
    "press": gui.UIFlatButton.UIStyle(bg=arcade.color.BITTER_LEMON),
}



CELL_SIZE = 50

# This sets the margin between each cell
MARGIN = 2
# and the margin from the edge of the window to the cell
WINDOW_MARGIN = 5

# # if traversing the cells list for 81 cells, this will create a dictionary map which is fast
# def create_cell_map(cells: List[Tuple[int,int]]) -> Dict[Tuple[int,int],int]:
#     """given cells list, it creates a grid used to find the cells when clicked
#     this function is meant to replace the index function, if it is too slow"""
#     # we will have already checked that the cells are unique
#     grid = {}
#     for i,cell in enumerate(cells):
#         grid[cell] = i




class SudokuWindow(arcade.Window):
    def __init__(self,puzzle: Puzzle, engine: ProofEngine):
        # using the puzzle def (the cell layout) calculate the window width and height
        self.puzzle = puzzle
        del puzzle
        
        rows, cols = zip(*self.puzzle.cell_layout)
        self.row_count = max(rows)+1
        self.column_count = max(cols)+1

        self.puzzle_width = (CELL_SIZE*self.column_count+MARGIN*(self.column_count+1))
        self.puzzle_height = (CELL_SIZE*self.row_count+MARGIN*(self.row_count+1))
        width = self.puzzle_width+300+WINDOW_MARGIN*2
        height = self.puzzle_height+50+WINDOW_MARGIN*2
        # these are selfed in the super constructor
        super().__init__(width,height,title="Sudoku Prover")
        
        self.set_location(210,251)

        self.engine = engine
        
        # self.mode = 'mouse'
        # self.function_args = []
        # self.selected_cell = None
        self.background_color = arcade.color.WHITE_SMOKE
        self.shape_list: arcade.shape_list.ShapeElementList[Any] = arcade.shape_list.ShapeElementList()
        self.digits_text_grid: List[arcade.Text] = [None for _ in range(self.puzzle.cell_count)] # type: ignore
        self.digits_batch = Batch()
        self.cand_text_grid: List[List[arcade.Text]] = [[None for _ in range(9)] for _ in range(self.puzzle.cell_count)] # type: ignore
        self.cand_batch = Batch()

        self.proof_text = arcade.Text(
            text="",x=self.puzzle_width+WINDOW_MARGIN*2,y=self.height-MARGIN,
            width=1000,
            color=arcade.color.BLACK,
            font_size=10,
            font_name=('Victor Mono','Menlo','monospace'),
            anchor_x="left",anchor_y="top",
            multiline=True
        )
        # init everything that needs to be done for each cell
        for i in range(self.puzzle.cell_count):
            x,y = self.get_cell_coords(i)
            rect = arcade.shape_list.create_rectangle_filled(x, y, CELL_SIZE, CELL_SIZE, arcade.color.WHITE)
            self.shape_list.append(rect)

            self.digits_text_grid[i] = arcade.Text(
                text="",x=x,y=y+int(0.12*CELL_SIZE),
                color=arcade.color.BLACK,
                font_size=30,
                font_name=("Chalkboard SE","calibri"),
                anchor_x="center",anchor_y="center",
                batch=self.digits_batch,
            )
            for d in range(9):
                ex = x + CELL_SIZE/3 * (d%3-1)
                ey = y - CELL_SIZE/3 * (d//3-1) - 0.05*CELL_SIZE
                self.cand_text_grid[i][d] = arcade.Text(
                    text="",x=ex,y=ey+int(0.12*CELL_SIZE),
                    color=arcade.color.BLUE,
                    font_size=15,
                    font_name=("Chalkboard SE","calibri"),
                    anchor_x="center",anchor_y="center",
                    batch=self.cand_batch,
                )
        # update the UI with current state
        self.refresh()

        self.terminal_ready = threading.Event()
        self.cmd_waiting: str = ''
        self.terminal_thread = threading.Thread(target=self.terminal_listener, daemon=True)
        self.terminal_thread.start()
        self.terminal_ready.set()

        self.ui = gui.UIManager()
        self.mode_row = gui.UIButtonRow(vertical=False,space_between=10,width=self.puzzle_width,height=CELL_SIZE-10,size_hint=None)
        button_mouse = self.mode_row.add_button('mouse',size_hint=(1,1))
        button_single = self.mode_row.add_button('fill ns',size_hint=(1,1))
        button_candidate = self.mode_row.add_button('toggle',size_hint=(1,1))

        anchor = self.ui.add(gui.UIAnchorLayout())
        anchor.add(self.mode_row,anchor_x="left",anchor_y="bottom",align_y=WINDOW_MARGIN,align_x=WINDOW_MARGIN)

        for btn in self.mode_row.children:
            btn.on_click = self.handle_mode_change
        self.mode: str = "mouse"
        self.update_mode_button_style()

        self.ui.enable()

    def refresh(self):
        """grabs state from the engine and fully updates the UI"""
        grid = self.engine.current.grid
        eliminations = self.engine.current.eliminations
        # maybe get the proof state too...maybe
        for cell in range(self.puzzle.cell_count):
            do_candidates = grid[cell] is None
            self.digits_text_grid[cell].text = grid[cell] if not do_candidates else ''

            for digit in self.engine.puzzle.symbols_python:
                if do_candidates:
                    if cell in eliminations and digit in eliminations[cell]:
                        self.cand_text_grid[cell][digit].text = ''
                    else:
                        self.cand_text_grid[cell][digit].text = digit
                else:
                    # no candidates show
                    self.cand_text_grid[cell][digit].text = ''

        if not self.engine.current.proof_state.goals:
            # proof finished
            self.proof_text.text = 'Proof finished!'
        else:
            proof_state = self.engine.current.proof_state.goals[0]
            proof_text = ''
            if proof_state.name is not None:
                proof_text += f'case {proof_state.name}\n'
            
            for var in proof_state.variables:
                # don't output these
                if var.name in ['k','H','S']:
                    continue
                
                proof_text += f'{var.name} : {var.t}\n'
            
            proof_text += f'⊢ {proof_state.target}'

            self.proof_text.text = proof_text

    def get_cell_coords(self, index: int):
        """gets the center pixel coordinates for a cell at index"""
        row, col = self.puzzle.cell_layout[index]
        x = WINDOW_MARGIN+MARGIN+(CELL_SIZE/2)+(CELL_SIZE+MARGIN)*col
        y = self.height-(WINDOW_MARGIN+MARGIN+(CELL_SIZE/2)+(CELL_SIZE+MARGIN)*row)
        return (x,y)
    
    def coords_to_grid_cell(self,x:int,y:int) -> int | None:
        """Finds the cell at the coord x,y"""
        x = x - WINDOW_MARGIN - MARGIN
        y = self.height - y - WINDOW_MARGIN - MARGIN
        # x and y are now at the top left at (0,0)
        # anything 0 to cell_size is a valid position
        col = x // (CELL_SIZE+MARGIN)
        x_in_cell = x % (CELL_SIZE+MARGIN) <= CELL_SIZE
        row = y // (CELL_SIZE+MARGIN)
        y_in_cell = y % (CELL_SIZE+MARGIN) <= CELL_SIZE

        if x_in_cell and y_in_cell:
            try:
                return self.puzzle.cell_layout.index((row,col))
            except:
                pass
        return None


    # def change_cell(self,index:int, value:Optional[int]):
    #     self.grid[index] = value
    #     self.digits_text_grid[index].text = str(value) if value is not None else ""

    # def update_elims_text(self):
    #     for cell,elims in eliminations.items():
    #         for digit in elims.keys():
    #             if self.grid[cell] is None:
    #                 self.cand_text_grid[cell][digit-1].text = str(digit)
    #             else:
    #                 # if the digit is placed, remove the elim shown
    #                 self.cand_text_grid[cell][digit-1].text = ""

    # def update_cell(self,index:int,value:Optional[int]):
    #     # check for validity
    #     raise NotImplementedError('update cell is no longer implemented')
    #     if value is None:
    #         print('setting a cell back to empty is not supported at the moment')
    #         return
    #         # self.change_cell(index,value)
    #         # return

    def on_update(self, delta_time: float) -> bool | None:
        # check for a cli command to run
        if self.terminal_ready.is_set():
            # if the terminal is still ready
            # there is no command
            return
        # if the terminal is not ready, there is a command
        # process it
        
        self.run_command_list([self.cmd_waiting])

        # terminal can go
        self.terminal_ready.set()


    def on_draw(self):
        self.clear()

        # draws all the cell dividers with one simple trick
        # until we have odd shaped puzzles...

        arcade.draw_rect_filled(arcade.LBWH(WINDOW_MARGIN,self.height-self.puzzle_height-WINDOW_MARGIN,self.puzzle_width,self.puzzle_height),arcade.color.BLACK)

        # draw cells
        self.shape_list.draw()
        # draw region dividers
        # assert ROW_COUNT == 9 and COLUMN_COUNT == 9, "region divider code depends on 9x9 grid"
        # x1 = WINDOW_MARGIN+MARGIN+3*(CELL_SIZE+MARGIN)-MARGIN/2
        # x2 = WINDOW_MARGIN+MARGIN+6*(CELL_SIZE+MARGIN)-MARGIN/2
        # arcade.draw_line(x1,WINDOW_MARGIN,x1,WINDOW_HEIGHT-WINDOW_MARGIN,arcade.color.BLACK,4)
        # arcade.draw_line(x2,WINDOW_MARGIN,x2,WINDOW_HEIGHT-WINDOW_MARGIN,arcade.color.BLACK,4)
        # y1 = WINDOW_MARGIN+MARGIN+3*(CELL_SIZE+MARGIN)-MARGIN/2
        # y2 = WINDOW_MARGIN+MARGIN+6*(CELL_SIZE+MARGIN)-MARGIN/2
        # arcade.draw_line(WINDOW_MARGIN,y1,WINDOW_MARGIN+9*(MARGIN+CELL_SIZE)+MARGIN,y1,arcade.color.BLACK,4)
        # arcade.draw_line(WINDOW_MARGIN,y2,WINDOW_MARGIN+9*(MARGIN+CELL_SIZE)+MARGIN,y2,arcade.color.BLACK,4)

        # draw digits
        self.digits_batch.draw()
        self.cand_batch.draw()
        self.proof_text.draw()
        # draw selector
        # if self.selected_cell is not None:
        #     x,y = center_coords(self.selected_cell)
        #     arcade.draw_rect_outline(arcade.XYWH(x,y,0.85*CELL_SIZE,0.85*CELL_SIZE),arcade.color.BLUE,3)
        # draw ui stuff
        self.ui.draw()

    def terminal_listener(self):
        while True:
            self.terminal_ready.wait()
            # print(self.engine.current.proof_state.goals[0])
            cmd = input(f'{self.engine.terminal_prompt}{' ' if self.engine.terminal_prompt else ''}> ').strip()
            self.cmd_waiting = cmd
            self.terminal_ready.clear()

    def handle_mode_change(self, event):
        self.mode = event.source.text
        print(f"mode changed to {self.mode}")
        self.update_mode_button_style()
    
    def update_mode_button_style(self):
        for btn in self.mode_row.children:
            if btn.text == self.mode:
                btn.style = ACTIVE_STYLE
            else:
                btn.style = NORMAL_STYLE

    def on_mouse_press(self, x: int, y: int, button: int, modifiers: int):
        # get the cell
        cell = self.coords_to_grid_cell(x,y)
        if cell is None:
            print('mouse press',x,y)
            # no cell pressed, carry on
            return
        # cell pressed
        print('mouse press cell',cell)
        match self.mode:
            case 'mouse':
                # nothing for this yet
                pass
            case 'fill ns':
                self.run_command_list([f'naked_single {cell}'])
            case 'toggle':
                pass
            case _:
                raise ValueError(f'unknown solve mode {self.mode}, did you forget to change some mode text?')
        

    # def on_key_press(self, symbol, modifiers): # type: ignore
    #     if self.selected_cell is not None and arcade.key.KEY_1 <= symbol <= arcade.key.KEY_9:
    #         digit = int(chr(symbol))
    #         self.update_cell(self.selected_cell,digit)

    def run_command_list(self,commands: List[str]):
        """runs the command and updates then refreshes the screen"""
        try:
            for cmd in commands:
                self.engine.command(cmd)
        except SystemExit:
            # Catch the exit(0) call and tell Arcade to die
            arcade.exit()
            return
        except Exception as e:
            # If you want it to hard-crash on other errors too:
            print(e)
            arcade.exit()
            return

        self.refresh()



def main(puzzle: Puzzle,engine: ProofEngine):
    window = SudokuWindow(puzzle,engine) # pyright: ignore[reportUnusedVariable]

    # Start the arcade game loop
    arcade.run()
