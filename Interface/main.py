# Python Arcade array template

from typing import Any, List, Optional

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
        self.selected_cell = None
        self.shape_list: arcade.shape_list.ShapeElementList[Any] = arcade.shape_list.ShapeElementList()
        self.digits_text_grid: List[arcade.Text] = [None for _ in range(CELLS)] # type: ignore
        self.digits_batch = Batch()
        self.background_color = arcade.color.WHITE_SMOKE
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

    def update_cell(self,index:int,value:Optional[int]):
        self.grid[index] = value
        self.digits_text_grid[index].text = str(value) if value is not None else ""

    def on_draw(self):
        self.clear()

        arcade.draw_rect_filled(arcade.LBWH(WINDOW_MARGIN,WINDOW_MARGIN,(CELL_SIZE*COLUMN_COUNT+MARGIN*(COLUMN_COUNT+1)),(CELL_SIZE*ROW_COUNT+MARGIN*(ROW_COUNT+1))),arcade.color.BLACK)


        # Draw the shapes representing our current grid
        self.shape_list.draw()
        self.digits_batch.draw()
        if self.selected_cell is not None:
            x,y = center_coords(self.selected_cell)
            arcade.draw_rect_outline(arcade.XYWH(x,y,CELL_SIZE,CELL_SIZE),arcade.color.BLUE,3)

                
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
            self.update_cell(self.selected_cell,int(chr(symbol)))
        

def main():
    """ Main function """
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
