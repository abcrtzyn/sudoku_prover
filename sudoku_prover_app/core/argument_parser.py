


from typing import TYPE_CHECKING, Any, List

if TYPE_CHECKING:
    from sudoku_prover_app.core.proof_engine import ProofEngine


def parse_args(engine: ProofEngine, params_string: str, arg_types: List[str]):
    params = params_string.split()
    num_params = len(params)

    parsed_args: List[Any] = []

    # parse arguments
    
    for t in arg_types:
        match t:
            case 'cell':
                cell = int(params.pop(0))
                if not (0 <= cell < engine.puzzle.cell_count):
                    raise ValueError(f'cell {cell} out of range')
                parsed_args.append(cell)
            case 'symbol':
                symbol = params.pop(0)
                # check that the param is actually in the puzzle symbols
                # currently, they are either strings or ints
                # first we check if the string works
                # if that doesn't work, we try to convert it to an int and try that.
                if symbol in engine.puzzle.symbols_python:
                    parsed_args.append(symbol)
                elif int(symbol) in engine.puzzle.symbols_python:
                    parsed_args.append(int(symbol))
                else:
                    raise ValueError(f'symbol {symbol} not in symbols')
            case 'term':
                term = params.pop(0)
                parsed_args.append(term)
            case 'line':
                # takes the rest of the line after the previous argument
                # I'm not using join because I want to preserve user spacing (not necessary, but I like it)
                params_used = num_params - len(params)
                line = params_string.split(' ',params_used)[-1].strip()
                params = [] # this uses up the rest of the params
                parsed_args.append(line)
            case _:
                assert False, f'Unkwown argument type {t} in the argument parser, the registry should not have allowed this'
    if params:
        raise ValueError(f'Too many arguments given, had "{params}" left')

    return parsed_args
