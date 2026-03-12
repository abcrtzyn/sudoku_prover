import SudokuLean.Basic
import SudokuLean.Symbols9
-- this file has common puzzle baselines to save some lines of text I'd say

set_option linter.style.whitespace false

-- Normal Sudoku Rules Apply!
structure NormalSudoku (solution: Nat -> Symbols9) where
  row1: UniqueSet solution { 0, 1, 2, 3, 4, 5, 6, 7, 8}
  row2: UniqueSet solution { 9,10,11,12,13,14,15,16,17}
  row3: UniqueSet solution {18,19,20,21,22,23,24,25,26}
  row4: UniqueSet solution {27,28,29,30,31,32,33,34,35}
  row5: UniqueSet solution {36,37,38,39,40,41,42,43,44}
  row6: UniqueSet solution {45,46,47,48,49,50,51,52,53}
  row7: UniqueSet solution {54,55,56,57,58,59,60,61,62}
  row8: UniqueSet solution {63,64,65,66,67,68,69,70,71}
  row9: UniqueSet solution {72,73,74,75,76,77,78,79,80}
  col1: UniqueSet solution { 0, 9,18,27,36,45,54,63,72}
  col2: UniqueSet solution { 1,10,19,28,37,46,55,64,73}
  col3: UniqueSet solution { 2,11,20,29,38,47,56,65,74}
  col4: UniqueSet solution { 3,12,21,30,39,48,57,66,75}
  col5: UniqueSet solution { 4,13,22,31,40,49,58,67,76}
  col6: UniqueSet solution { 5,14,23,32,41,50,59,68,77}
  col7: UniqueSet solution { 6,15,24,33,42,51,60,69,78}
  col8: UniqueSet solution { 7,16,25,34,43,52,61,70,79}
  col9: UniqueSet solution { 8,17,26,35,44,53,62,71,80}
  box1: UniqueSet solution { 0, 1, 2, 9,10,11,18,19,20}
  box2: UniqueSet solution { 3, 4, 5,12,13,14,21,22,23}
  box3: UniqueSet solution { 6, 7, 8,15,16,17,24,25,26}
  box4: UniqueSet solution {27,28,29,36,37,38,45,46,47}
  box5: UniqueSet solution {30,31,32,39,40,41,48,49,50}
  box6: UniqueSet solution {33,34,35,42,43,44,51,52,53}
  box7: UniqueSet solution {54,55,56,63,64,65,72,73,74}
  box8: UniqueSet solution {57,58,59,66,67,68,75,76,77}
  box9: UniqueSet solution {60,61,62,69,70,71,78,79,80}
