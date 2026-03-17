import threading
from typing import Any, Dict, List
from pyglet.graphics import Batch
import arcade

from sudoku_prover_ui.proof_engine import ProofEngine


"""HARD CODING EVERYTHING ABOUT THE PUZZLE FOR THE MOMENT"""

# Set how many rows and columns we will have
ROW_COUNT = 4
COLUMN_COUNT = 4
CELLS = ROW_COUNT * COLUMN_COUNT

puzzle = """structure TestPuzzle (solution: Nat -> Symbols4) where
  row1: UniqueSet solution { 0, 1, 2, 3}
  row2: UniqueSet solution { 4, 5, 6, 7}
  row3: UniqueSet solution { 8, 9,10,11}
  row4: UniqueSet solution {12,13,14,15}
  col1: UniqueSet solution { 0, 4, 8,12}
  col2: UniqueSet solution { 1, 5, 9,13}
  col3: UniqueSet solution { 2, 6,10,14}
  col4: UniqueSet solution { 3, 7,11,15}
  box1: UniqueSet solution { 0, 1, 4, 5}
  box2: UniqueSet solution { 2, 3, 6, 7}
  box3: UniqueSet solution { 8, 9,12,13}
  box4: UniqueSet solution {10,11,14,15}
  given2: solution 2 = 4
  given4: solution 4 = 4
  given6: solution 6 = 3
  given9: solution 9 = 4
  given11: solution 11 = 3
  given13: solution 13 = 1
  outside_grid: ∀ x, x ≥ 16 -> solution x = Symbols4.one -- just need something to call default
"""

# This sets the WIDTH and HEIGHT of each grid location
CELL_SIZE = 50

givens = {
    2: 4,
    4: 4,
    6: 3,
    9: 4,
    11: 3,
    13: 1,
}

regions: Dict[str,List[int]] = {
    'row1': [ 0, 1, 2, 3],
    'row2': [ 4, 5, 6, 7],
    'row3': [ 8, 9,10,11],
    'row4': [12,13,14,15],
    'col1': [ 0, 4, 8,12],
    'col2': [ 1, 5, 9,13],
    'col3': [ 2, 6,10,14],
    'col4': [ 3, 7,11,15],
    'box1': [ 0, 1, 4, 5],
    'box2': [ 2, 3, 6, 7],
    'box3': [ 8, 9,12,13],
    'box4': [10,11,14,15],
}
givens = {
    2: 4,
    4: 4,
    6: 3,
    9: 4,
    11: 3,
    13: 1,
}

regions_search: List[List[str]] = []

def generate_search():
    for _ in range(81):
        regions_search.append([])
    for r in regions:
        for c in regions[r]:
            regions_search[c].append(r)

generate_search()

"""END HARDCODING THE PUZZLE"""



# This sets the margin between each cell
MARGIN = 2

WINDOW_MARGIN = 5

WINDOW_WIDTH = (CELL_SIZE*COLUMN_COUNT+MARGIN*(COLUMN_COUNT+1))+WINDOW_MARGIN+300
WINDOW_HEIGHT = (CELL_SIZE*ROW_COUNT+MARGIN*(ROW_COUNT+1))+WINDOW_MARGIN*2


def center_coords(i: int):
    # center coords of the rectangle
    x = WINDOW_MARGIN+MARGIN+(CELL_SIZE/2)+(CELL_SIZE+MARGIN)*(i%COLUMN_COUNT)
    y = WINDOW_MARGIN+MARGIN+(CELL_SIZE/2)+(CELL_SIZE+MARGIN)*((ROW_COUNT-1)-i//COLUMN_COUNT)
    return (x,y)

def coords_to_grid_cell(x:int,y:int):
    x = x - WINDOW_MARGIN - MARGIN
    y = WINDOW_HEIGHT - y - WINDOW_MARGIN - MARGIN
    # x and y are now at the top left of the 0th cell
    # anything 0 to cell_size is a valid position
    col = x // (CELL_SIZE+MARGIN)
    x_in_cell = x % (CELL_SIZE+MARGIN) <= CELL_SIZE
    row = y // (CELL_SIZE+MARGIN)
    y_in_cell = y % (CELL_SIZE+MARGIN) <= CELL_SIZE
    if 0 <= col < COLUMN_COUNT and 0 <= row < ROW_COUNT and x_in_cell and y_in_cell:
        return row*COLUMN_COUNT+col
    else:
        return None


WINDOW_TITLE = "Sudoku Prover"


class SudokuWindow(arcade.Window):
    def __init__(self,width: int,height: int,title: str | None):
        super().__init__(width,height,title)
        # set up the proof engine which creates the initial state
        print('starting up Lean Server',end=' ')
        self.engine = ProofEngine(CELLS,puzzle)
        print('done')
        self.set_location(210,251)



        # self.mode = 'mouse'
        # self.function_args = []
        # self.selected_cell = None
        self.background_color = arcade.color.WHITE_SMOKE
        self.shape_list: arcade.shape_list.ShapeElementList[Any] = arcade.shape_list.ShapeElementList()
        self.digits_text_grid: List[arcade.Text] = [None for _ in range(CELLS)] # type: ignore
        self.digits_batch = Batch()
        self.cand_text_grid: List[List[arcade.Text]] = [[None for _ in range(9)] for _ in range(CELLS)] # type: ignore
        self.cand_batch = Batch()

        self.proof_text = arcade.Text(
            text="",x=WINDOW_HEIGHT,y=WINDOW_HEIGHT-MARGIN,
            width=1000,
            color=arcade.color.BLACK,
            font_size=10,
            font_name=('Victor Mono','Menlo','monospace'),
            anchor_x="left",anchor_y="top",
            multiline=True
        )
        # init everything that needs to be done for each cell
        for i in range(CELLS):
            x,y = center_coords(i)
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
        self.terminal_prompt = next(self.engine.active_gen)
        self.terminal_thread = threading.Thread(target=self.terminal_listener, daemon=True)
        self.terminal_thread.start()
        self.terminal_ready.set()

    def refresh(self):
        """grabs state from the engine and fully updates the UI"""
        grid = self.engine.current.grid
        eliminations = self.engine.current.eliminations
        proof_state = self.engine.current.proof_state.goals[0]
        # maybe get the proof state too...maybe
        for cell in range(CELLS):
            do_candidates = grid[cell] is None
            self.digits_text_grid[cell].text = grid[cell] if not do_candidates else ''

            for digit in self.engine.symbols:
                if do_candidates:
                    if cell in eliminations and digit in eliminations[cell]:
                        self.cand_text_grid[cell][digit].text = ''
                    else:
                        self.cand_text_grid[cell][digit].text = digit
                else:
                    # no candidates show
                    self.cand_text_grid[cell][digit].text = ''
        
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
        try:
            self.terminal_prompt = self.engine.active_gen.send(self.cmd_waiting)
        except SystemExit:
            # Catch the exit(0) call and tell Arcade to die
            arcade.exit()
            return
        except Exception as e:
            # If you want it to hard-crash on other errors too:
            print(e)
            arcade.exit()
            return
        
        # gone through the states, we may or may not have an active proof
        
        # update the UI crudely
        self.refresh()
        # terminal can go
        self.terminal_ready.set()


    def on_draw(self):
        self.clear()

        arcade.draw_rect_filled(arcade.LBWH(WINDOW_MARGIN,WINDOW_MARGIN,(CELL_SIZE*COLUMN_COUNT+MARGIN*(COLUMN_COUNT+1)),(CELL_SIZE*ROW_COUNT+MARGIN*(ROW_COUNT+1))),arcade.color.BLACK)

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

    def terminal_listener(self):
        while True:
            self.terminal_ready.wait()
            print(self.engine.current.proof_state.goals[0])
            cmd = input(f'{self.terminal_prompt}{' ' if self.terminal_prompt else ''}> ').strip()
            self.cmd_waiting = cmd
            self.terminal_ready.clear()

    # def on_mouse_press(self, x, y, button, modifiers):
        # first, check for mode switch
        # if on a mode button
        # if button := False:
        #     print(f'click mode {button}')
        #     self.mode = button
        #     # reset args
        #     self.function_args = []
        #     return
        # # if it wasn't selecting a new mode

        # # Convert the clicked mouse position into grid coordinates
        # if index := coords_to_grid_cell(x,y):
        #     print(f'click cell {index}')
        #     if self.mode == 'mouse':
        #         if index == self.selected_cell:
        #             self.selected_cell = None
        #         else:
        #             self.selected_cell = index
        #     else:
        #         # TODO check for correct call signiture first
        #         self.function_args.append(('cell',index))

        # check for correct number of args


    # def on_key_press(self, symbol, modifiers): # type: ignore
    #     if self.selected_cell is not None and arcade.key.KEY_1 <= symbol <= arcade.key.KEY_9:
    #         digit = int(chr(symbol))
    #         self.update_cell(self.selected_cell,digit)




def main():
    window = SudokuWindow(WINDOW_WIDTH, WINDOW_HEIGHT, WINDOW_TITLE) # pyright: ignore[reportUnusedVariable]

    # Start the arcade game loop
    arcade.run()
