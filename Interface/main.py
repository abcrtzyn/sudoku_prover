# Python Arcade array template

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
eliminations: Dict[Tuple[int,int],str] = {}

def find_conflict(grid:List[Optional[int]], cell: int, digit: int):
    if grid[cell] is not None:
        if grid[cell] != digit:
            return True # digit in cell conflict
        else:
            print(f'bad input, cell {cell} has {digit}')
            return False
    # else
    # check for digits in regions
    for r in regions_search[cell]:
        for i in regions[r]:
            if grid[i] == digit:
                # digit in region r
                return True
    if (cell,digit) in eliminations:
        return True
    print(f'could not find a conflict for cell {cell} with digit {digit}')
    return False


def handle_naked_single(grid: List[Optional[int]], cell: int, digit: int):
    for d in range(1,10):
        if d != digit:
            if not find_conflict(grid,cell,d):
                return False
    return True


def handle_hidden_single(grid: List[Optional[int]], cell: int, digit: int):
    for region in regions_search[cell]:
        # try each region for a hidden single
        for i in regions[region]:
            if i != cell and not find_conflict(grid,i,digit):
                # not a hidden single in this region
                break
        else:
            # did not break early
            # valid hidden single in this region
            return True
    return False



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


class SudokuWindow(arcade.View):
    def __init__(self):
        super().__init__()
        self.grid: List[Optional[int]] = [None for _ in range(CELLS)]
        self.background_color = arcade.color.WHITE_SMOKE

        self.reset_grid()
    
    def reset_grid(self):
        self.selected_cell = None
        self.shape_list: arcade.shape_list.ShapeElementList[Any] = arcade.shape_list.ShapeElementList()
        self.digits_text_grid: List[arcade.Text] = [None for _ in range(CELLS)] # type: ignore
        self.digits_batch = Batch()
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
        for i,x in givens.items():
            self.change_cell(i,x)

    def change_cell(self,index:int, value:Optional[int]):
        self.grid[index] = value
        self.digits_text_grid[index].text = str(value) if value is not None else ""

    def update_cell(self,index:int,value:Optional[int]):
        # check for validity
        if value is None:
            self.change_cell(index,value)
            return
        
        if handle_naked_single(self.grid,index,value):
            self.change_cell(index,value)
            return
        if handle_hidden_single(self.grid,index,value):
            self.change_cell(index,value)
            return
        print(f'could not find a reason to place digit {value} in cell {index}')

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
        # draw selector
        if self.selected_cell is not None:
            x,y = center_coords(self.selected_cell)
            arcade.draw_rect_outline(arcade.XYWH(x,y,CELL_SIZE,CELL_SIZE),arcade.color.BLUE,3)
        # draw ui stuff


                
    def on_mouse_press(self, x, y, button, modifiers):
        # Convert the clicked mouse position into grid coordinates
        index = coords_to_grid_cell(x,y)
        if index is None:
            return
        print(f'click cell {index}')
        # if selected, deselect, else, select
        if index == self.selected_cell:
            self.selected_cell = None
        else:
            self.selected_cell = index

    def on_key_press(self, symbol, modifiers):
        if self.selected_cell is not None and arcade.key.KEY_1 <= symbol <= arcade.key.KEY_9:
            digit = int(chr(symbol))
            self.update_cell(self.selected_cell,digit)

    


def main():
    # Create a window class. This is what actually shows up on screen
    window = arcade.Window(WINDOW_WIDTH, WINDOW_HEIGHT, WINDOW_TITLE)

    # Create the GameView
    game = SudokuWindow()

    # Show GameView on screen
    window.show_view(game)

    # Start the arcade game loop
    arcade.run()


if __name__ == "__main__":
    main()
