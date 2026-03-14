# Python Arcade array template

import queue
import threading
from time import sleep
from typing import Any, Dict, List, Optional, Tuple

# import pyglet
# pyglet.options['dpi_scaling'] = 'real'
from pyglet.graphics import Batch

import arcade

# Set how many rows and columns we will have
ROW_COUNT = 9
COLUMN_COUNT = 9
CELLS = ROW_COUNT * COLUMN_COUNT

# This sets the WIDTH and HEIGHT of each grid location
CELL_SIZE = 50

# This sets the margin between each cell
MARGIN = 2

WINDOW_MARGIN = 5

WINDOW_WIDTH = (CELL_SIZE*COLUMN_COUNT+MARGIN*(COLUMN_COUNT+1))+WINDOW_MARGIN+200
WINDOW_HEIGHT = (CELL_SIZE*ROW_COUNT+MARGIN*(ROW_COUNT+1))+WINDOW_MARGIN*2

givens = {
    1: 3,
    5: 7,
    10: 6,
    11: 7,
    12: 1,
    15: 3,
    16: 5,
    19: 1,
    20: 9,
    27: 5,
    35: 7,
    37: 7,
    39: 2,
    41: 3,
    43: 1,
    45: 9,
    53: 8,
    60: 6,
    61: 8,
    64: 8,
    65: 6,
    68: 2,
    69: 9,
    70: 7,
    75: 7,
    79: 4,
}

regions: Dict[str,List[int]] = {
    'row1': [ 0, 1, 2, 3, 4, 5, 6, 7, 8],
    'row2': [ 9,10,11,12,13,14,15,16,17],
    'row3': [18,19,20,21,22,23,24,25,26],
    'row4': [27,28,29,30,31,32,33,34,35],
    'row5': [36,37,38,39,40,41,42,43,44],
    'row6': [45,46,47,48,49,50,51,52,53],
    'row7': [54,55,56,57,58,59,60,61,62],
    'row8': [63,64,65,66,67,68,69,70,71],
    'row9': [72,73,74,75,76,77,78,79,80],
    'col1': [ 0, 9,18,27,36,45,54,63,72],
    'col2': [ 1,10,19,28,37,46,55,64,73],
    'col3': [ 2,11,20,29,38,47,56,65,74],
    'col4': [ 3,12,21,30,39,48,57,66,75],
    'col5': [ 4,13,22,31,40,49,58,67,76],
    'col6': [ 5,14,23,32,41,50,59,68,77],
    'col7': [ 6,15,24,33,42,51,60,69,78],
    'col8': [ 7,16,25,34,43,52,61,70,79],
    'col9': [ 8,17,26,35,44,53,62,71,80],
    'box1': [ 0, 1, 2, 9,10,11,18,19,20],
    'box2': [ 3, 4, 5,12,13,14,21,22,23],
    'box3': [ 6, 7, 8,15,16,17,24,25,26],
    'box4': [27,28,29,36,37,38,45,46,47],
    'box5': [30,31,32,39,40,41,48,49,50],
    'box6': [33,34,35,42,43,44,51,52,53],
    'box7': [54,55,56,63,64,65,72,73,74],
    'box8': [57,58,59,66,67,68,75,76,77],
    'box9': [60,61,62,69,70,71,78,79,80]
}

regions_search: List[List[str]] = []

def generate_search():
    for _ in range(81):
        regions_search.append([])
    for r in regions:
        for c in regions[r]:
            regions_search[c].append(r)

generate_search()

# manual eliminations, automatic eliminations for naked single or hidden single
# will occur at the time
eliminations: Dict[int,Dict[int,str]] = {}


"""eliminates all of digit from every cell in every region that cell is a part of"""
def region_eliminate(cell: int,digit: int):
    for r in regions_search[cell]:
        for i in regions[r]:
            if i == cell:
                continue
            # we have a choice to override a current elimination rule, or keep the first one
            # there are pros and cons to either, but that is for future me to decide.
            # this code OVERRIDES existing elemination rules
            if i not in eliminations:
                eliminations[i] = dict()
            eliminations[i][digit] = f'digit_in_region: cell {cell} in region {r}'

"""returns the digit in a cell because it is the only candidate left

this function is not very protective, it currently only checks 1-9 and first checks for exactly 8 digit eliminations"""
def naked_single(cell: int):
    elims = eliminations[cell]
    if len(elims.keys()) != 8:
        return None
    # good length
    for d in range(1,10):
        if d not in elims.keys():
            return d
    raise ValueError(f'naked cell can\'t handle whatever happened. naked_cell({cell})')
    
"""returns the only cell where a digit appears in a region

this function is not very protective, it currently assumes that all regions have the surjective property"""
def hidden_single(grid: List[Optional[int]], digit: int, region: str):
    current_find = None
    for cell in regions[region]:
        if grid[cell] is not None:
            continue
        if cell in eliminations:
            if digit in eliminations[cell]:
                continue
        # else case for both, digit not eliminated
        if current_find is not None:
            # more than one cell is possible
            return None
        # else, set it
        current_find = cell
    # only one cell is not eliminated
    return current_find




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
        self.set_location(210,251)

        self.grid: List[Optional[int]] = [None for _ in range(CELLS)]
        self.background_color = arcade.color.WHITE_SMOKE

        self.reset_grid()
        self.cmd_queue: queue.Queue[str] = queue.Queue()
    
        threading.Thread(target=self.terminal_listener, daemon=True).start()

    def reset_grid(self):
        self.mode = 'mouse'
        self.function_args = []
        self.selected_cell = None
        self.shape_list: arcade.shape_list.ShapeElementList[Any] = arcade.shape_list.ShapeElementList()
        self.digits_text_grid: List[arcade.Text] = [None for _ in range(CELLS)] # type: ignore
        self.digits_batch = Batch()
        self.elims_text_grid: List[List[arcade.Text]] = [[None for _ in range(9)] for _ in range(CELLS)] # type: ignore
        self.elims_batch = Batch()
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
                self.elims_text_grid[i][d] = arcade.Text(
                    text="",x=ex,y=ey+int(0.12*CELL_SIZE),
                    color=arcade.color.RED,
                    font_size=15,
                    font_name=("Chalkboard SE","calibri"),
                    anchor_x="center",anchor_y="center",
                    batch=self.elims_batch,
                )
        
        for i,x in givens.items():
            self.change_cell(i,x)
            region_eliminate(i,x)
        self.update_elims_text()

    def change_cell(self,index:int, value:Optional[int]):
        self.grid[index] = value
        self.digits_text_grid[index].text = str(value) if value is not None else ""

    def update_elims_text(self):
        for cell,elims in eliminations.items():
            for digit in elims.keys():
                if self.grid[cell] is None:
                    self.elims_text_grid[cell][digit-1].text = str(digit)
                else:
                    # if the digit is placed, remove the elim shown
                    self.elims_text_grid[cell][digit-1].text = ""

    def update_cell(self,index:int,value:Optional[int]):
        # check for validity
        raise NotImplementedError('update cell is no longer implemented')
        if value is None:
            print('setting a cell back to empty is not supported at the moment')
            return
            # self.change_cell(index,value)
            # return
        

    def on_update(self, delta_time: float) -> bool | None:
        # check for a cli command to run
        if not self.cmd_queue.empty():
            cmd = self.cmd_queue.get_nowait()
            args = cmd.split()            
            if args[0] == 'exit':
                arcade.exit()
            elif args[0] == 'loc':
                # this was to get the current location of the window
                # allows me to place the window wherever I want when it opens
                print(self.get_location())
            elif args[0] == 'naked' and 2 <= len(args):
                cell = int(args[1])
                # naked takes a cell number, anything after is not used
                # the command succeeds if the cell only has one candidate
                if digit := naked_single(cell):
                    self.change_cell(cell,digit)
                    region_eliminate(cell,digit)
            elif args[0] == 'hidden' and 2 <= len(args):
                digit = int(args[1])
                region = args[2]
                # hidden takes a digit and region, anything after is not used
                # the command succeeds if the region only has one cell without digit eliminated
                if cell := hidden_single(self.grid,digit,region):
                    self.change_cell(cell, digit)
                    region_eliminate(cell,digit)
        self.update_elims_text()

                    

                
    
    def on_draw(self):
        self.clear()

        arcade.draw_rect_filled(arcade.LBWH(WINDOW_MARGIN,WINDOW_MARGIN,(CELL_SIZE*COLUMN_COUNT+MARGIN*(COLUMN_COUNT+1)),(CELL_SIZE*ROW_COUNT+MARGIN*(ROW_COUNT+1))),arcade.color.BLACK)

        # draw cells
        self.shape_list.draw()
        # draw region dividers
        assert ROW_COUNT == 9 and COLUMN_COUNT == 9, "region divider code depends on 9x9 grid"
        x1 = WINDOW_MARGIN+MARGIN+3*(CELL_SIZE+MARGIN)-MARGIN/2
        x2 = WINDOW_MARGIN+MARGIN+6*(CELL_SIZE+MARGIN)-MARGIN/2
        arcade.draw_line(x1,WINDOW_MARGIN,x1,WINDOW_HEIGHT-WINDOW_MARGIN,arcade.color.BLACK,4)
        arcade.draw_line(x2,WINDOW_MARGIN,x2,WINDOW_HEIGHT-WINDOW_MARGIN,arcade.color.BLACK,4)
        y1 = WINDOW_MARGIN+MARGIN+3*(CELL_SIZE+MARGIN)-MARGIN/2
        y2 = WINDOW_MARGIN+MARGIN+6*(CELL_SIZE+MARGIN)-MARGIN/2
        arcade.draw_line(WINDOW_MARGIN,y1,WINDOW_MARGIN+9*(MARGIN+CELL_SIZE)+MARGIN,y1,arcade.color.BLACK,4)
        arcade.draw_line(WINDOW_MARGIN,y2,WINDOW_MARGIN+9*(MARGIN+CELL_SIZE)+MARGIN,y2,arcade.color.BLACK,4)

        # draw digits
        self.digits_batch.draw()
        self.elims_batch.draw()
        # draw selector
        if self.selected_cell is not None:
            x,y = center_coords(self.selected_cell)
            arcade.draw_rect_outline(arcade.XYWH(x,y,0.85*CELL_SIZE,0.85*CELL_SIZE),arcade.color.BLUE,3)
        # draw ui stuff

    def terminal_listener(self):
        sleep(2)
        while True:
            cmd = input('> ')
            self.cmd_queue.put(cmd.strip().lower())
            
                
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


    def on_key_press(self, symbol, modifiers): # type: ignore
        if self.selected_cell is not None and arcade.key.KEY_1 <= symbol <= arcade.key.KEY_9:
            digit = int(chr(symbol))
            self.update_cell(self.selected_cell,digit)

    


def main():
    window = SudokuWindow(WINDOW_WIDTH, WINDOW_HEIGHT, WINDOW_TITLE)
    
    # Start the arcade game loop
    arcade.run()


if __name__ == "__main__":
    main()
