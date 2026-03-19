# this is the main file that the cli interacts with
# should have options for solve, edit, verify, edit from template, anything really

import sys


def main():
    # step 0 check for command line args
    args = sys.argv
    if len(args) != 2:
        print('please give a .suko file to use as input')


if __name__ == '__main__':
    main()
