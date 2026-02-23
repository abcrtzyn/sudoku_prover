import SudokuLean.Basic
-- this file has common puzzle baselines to save some lines of text I'd say

set_option linter.style.whitespace false

-- Normal Sudoku Rules Apply!
structure NormalSudoku (solution: Nat -> Symbols9) where
  row1: UniqueRegion solution { 0, 1, 2, 3, 4, 5, 6, 7, 8}
  row2: UniqueRegion solution { 9,10,11,12,13,14,15,16,17}
  row3: UniqueRegion solution {18,19,20,21,22,23,24,25,26}
  row4: UniqueRegion solution {27,28,29,30,31,32,33,34,35}
  row5: UniqueRegion solution {36,37,38,39,40,41,42,43,44}
  row6: UniqueRegion solution {45,46,47,48,49,50,51,52,53}
  row7: UniqueRegion solution {54,55,56,57,58,59,60,61,62}
  row8: UniqueRegion solution {63,64,65,66,67,68,69,70,71}
  row9: UniqueRegion solution {72,73,74,75,76,77,78,79,80}
  col1: UniqueRegion solution { 0, 9,18,27,36,45,54,63,72}
  col2: UniqueRegion solution { 1,10,19,28,37,46,55,64,73}
  col3: UniqueRegion solution { 2,11,20,29,38,47,56,65,74}
  col4: UniqueRegion solution { 3,12,21,30,39,48,57,66,75}
  col5: UniqueRegion solution { 4,13,22,31,40,49,58,67,76}
  col6: UniqueRegion solution { 5,14,23,32,41,50,59,68,77}
  col7: UniqueRegion solution { 6,15,24,33,42,51,60,69,78}
  col8: UniqueRegion solution { 7,16,25,34,43,52,61,70,79}
  col9: UniqueRegion solution { 8,17,26,35,44,53,62,71,80}
  box1: UniqueRegion solution { 0, 1, 2, 9,10,11,18,19,20}
  box2: UniqueRegion solution { 3, 4, 5,12,13,14,21,22,23}
  box3: UniqueRegion solution { 6, 7, 8,15,16,17,24,25,26}
  box4: UniqueRegion solution {27,28,29,36,37,38,45,46,47}
  box5: UniqueRegion solution {30,31,32,39,40,41,48,49,50}
  box6: UniqueRegion solution {33,34,35,42,43,44,51,52,53}
  box7: UniqueRegion solution {54,55,56,63,64,65,72,73,74}
  box8: UniqueRegion solution {57,58,59,66,67,68,75,76,77}
  box9: UniqueRegion solution {60,61,62,69,70,71,78,79,80}
