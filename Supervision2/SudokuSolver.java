package uk.ac.cam.cl.cm927.Strategies;

import java.util.Arrays;

public class SudokuSolver {
    private static int EMPTY = 0;

    public static void main(String[] args) {
        int[][] toSolve =
                {{8, 0, 0, 0, 0, 0, 0, 0, 0},
                 {0, 0, 3, 6, 0, 0, 0, 0, 0},
                 {0, 7, 0, 0, 9, 0, 2, 0, 0},
                 {0, 5, 0, 0, 0, 7, 0, 0, 0},
                 {0, 0, 0, 0, 4, 5, 7, 0, 0},
                 {0, 0, 0, 1, 0, 0, 0, 3, 0},
                 {0, 0, 1, 0, 0, 0, 0, 6, 8},
                 {0, 0, 8, 5, 0, 0, 0, 1, 0},
                 {0, 9, 0, 0, 0, 0, 4, 0, 0}};
        solve(toSolve);
        System.out.println(Arrays.deepToString(toSolve));
    }


    private static void solve(int[][] sudoku) {
        try {
            solveMethod(sudoku, sudoku, 0, 0);
        }
        catch (NotFound e) {
            System.out.println("No solution found");
        }
    }

    private static void solveMethod(int[][] sudoku, int[][] solution, int row, int col) throws NotFound {


        solution = copy(solution);
        boolean found = false;
        for (int toIns = 1; !found && toIns < 10; toIns++){
            if (valid(solution, row, col, toIns)) {
                found = true;
                solution[row][col] = toIns;
                try {
                    int newRow = row, newCol = col;
                    //Find the next empty slot
                    while ((newRow == row && newCol == col) || (sudoku[newRow][newCol] != EMPTY)) {
                        newCol++;
                        if (newCol > 8) {
                            newCol = 0;
                            newRow++;
                        }
                        if (row == 8 && col == 8){
                            for (int i = 0; i < 9; i++) {
                                sudoku[i] = solution[i];
                            }
                            return;
                        }
                    }
                    solveMethod(sudoku, solution, newRow, newCol);

                }
                catch (NotFound e) {
                    found = false;
                }
            }
        }
        if (!found){
            throw new NotFound();
        }
    }



    private static boolean valid(int[][] sudoku, int row, int col, int toIns) {
        for (int i = 0; i < sudoku[row].length; i++){
            if (sudoku[row][i] == toIns) return false;
        }
        for (int i = 0; i < sudoku.length; i++) {
            if (sudoku[i][col] == toIns) return false;
        }
        for (int i = row / 3 * 3; i < row / 3 * 3 + 3; i++) {
            for (int j = col / 3 * 3; j < col / 3 * 3 + 3; j++) {
                if (sudoku[i][j] == toIns) return false;
            }
        }
        return true;
    }


    private static int[][] copy(int[][] toCopy) {
        int[][] copy = new int[9][9];
        for (int i = 0; i < 9; i++) {
            copy[i] = toCopy[i].clone();
        }
        return copy;
    }

}
