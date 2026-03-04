from typing import Dict, List, Optional, Tuple
import re

# TODO steps
# step 1: we are starting with just a helper program to create the sudoku proof
#   I ask to fill a cell with naked logic, or hidden logic
# step 2: interface that shows the current state of the grid
# step 3: point and click interface





grid: List[Optional[int]] = [None]*81
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

def show_grid() -> None:
    str_grid = list(map(lambda x: ' ' if x is None else str(x), grid))

    print(' '.join(str_grid[0:3]),'|',' '.join(str_grid[3:6]),'|',' '.join(str_grid[6:9]))
    print(' '.join(str_grid[9:12]),'|',' '.join(str_grid[12:15]),'|',' '.join(str_grid[15:18]))
    print(' '.join(str_grid[18:21]),'|',' '.join(str_grid[21:24]),'|',' '.join(str_grid[24:27]))
    print('------+-------+------')
    print(' '.join(str_grid[27:30]),'|',' '.join(str_grid[30:33]),'|',' '.join(str_grid[33:36]))
    print(' '.join(str_grid[36:39]),'|',' '.join(str_grid[39:42]),'|',' '.join(str_grid[42:45]))
    print(' '.join(str_grid[45:48]),'|',' '.join(str_grid[48:51]),'|',' '.join(str_grid[51:54]))
    print('------+-------+------')
    print(' '.join(str_grid[54:57]),'|',' '.join(str_grid[57:60]),'|',' '.join(str_grid[60:63]))
    print(' '.join(str_grid[63:66]),'|',' '.join(str_grid[66:69]),'|',' '.join(str_grid[69:72]))
    print(' '.join(str_grid[72:75]),'|',' '.join(str_grid[75:78]),'|',' '.join(str_grid[78:81]))

def find_conflict(cell: int, digit: int):
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
        


def handle_naked_single(cell: int, digit: int):
    for d in range(1,10):
        if d == digit:
            pass
        elif not find_conflict(cell,d):
            return
    grid[cell] = digit


def handle_hidden_single(region: str, digit: int):
    if region not in regions:
        print(f'unknown region \'{region}\'')
        return
    cell = None
    for i in regions[region]:
        result = find_conflict(i,digit)
        if not result:
            if cell is None:
                cell = i
            else:
                print(f'more than one cell in {region} can have {digit}')
                return
    if cell is None:
        print(f'zero cells in {region} can have {digit}')
        return
    # one cell, good to go
    grid[cell] = digit

def handle_sorry_single(cell: int, digit: int):
    grid[cell] = digit
    pass


def handle_naked_locked_set(cell):
    pass





while True:
    show_grid()
    prompt = input('> ')
    if re.match('exit|off|quit',prompt):
        break
    # figue out this input
    elif mat := re.match('naked\\s+(\\d+)\\s+(\\d)',prompt):
        # naked 34 4 (naked single, uses any digits in regions and manual eliminations)
        handle_naked_single(int(mat.group(1)),int(mat.group(2)))
    elif mat := re.match('hidden\\s+(\\S+)\\s+(\\d)',prompt):
        # hidden box3 4 (hidden single, uses any digit in cells or digit in regions or manual eliminations)
        handle_hidden_single(mat.group(1),int(mat.group(2)))
    elif mat := re.match('sorry\\s+(\\d+)\\s+(\\d)',prompt):
        # sorry just fill the digit in
        handle_sorry_single(int(mat.group(1)),int(mat.group(2)))
    elif mat := re.match('not\\s+(\\d+)\\s+(\\d)\\s+(.+)',prompt):
        # not 34 6 (elimination, give reason)
        eliminations[(int(mat.group(1)),int(mat.group(2)))] = mat.group(3)
    elif mat := re.match('locked\\s+naked\\s+(\\d+(\\s+\\d+)*)\\s*,\\s*(\\d(\\s+\\d)*)+',prompt):
        # locked naked cells, digits
        # groups 1 and 3 are cells and digits respectively
        # need to check that cells are all in the same region
        # check conflicts for every other digit in each cell
        pass
    elif mat := re.match('locked\\s+hidden\\s+(\\S+)\\s*,\\s*(\\d(\\s+\\d)*)+',prompt):
        # locked hidden region digits
        # check for conflicts in each cell, there should be exactly the same number of cells as digits
        pass
    else:
        print('unknown command')
    
    # ? support set ...
    
