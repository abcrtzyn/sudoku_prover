import os
import tempfile
from typing import Any, Dict, List, Tuple, cast
import leanclient as lc  # pyright: ignore[reportMissingTypeStubs]

# temp dir from the lean project path
TEMP_DIR = ".lean_temp"



def get_temp_file(project_root: str):
    """Creates a tempfile at [projoct_root]/[TEMP_DIR] and returns the relative path from cwd"""
    temp_dir = os.path.join(project_root, TEMP_DIR)
    os.makedirs(temp_dir, exist_ok=True)
    
    fd, path = tempfile.mkstemp(suffix=".lean", dir=temp_dir)
    os.close(fd) # close the handle, don't need it
    return path


def clear_temp_file(project_root: str, file_path: str):
    """Removes the tempfile given by file_path, then tries to remove the temp dir if there are no other files in the temp dir"""
    if os.path.exists(file_path):
        os.remove(file_path)
        
    temp_dir = os.path.join(project_root, TEMP_DIR)
    try:
        if os.path.exists(temp_dir) and not os.listdir(temp_dir):
            os.rmdir(temp_dir)
    except OSError:
        # Directory not empty, other instances are still running
        pass


class LeanLspRepl:
    def __init__(self, project_path: str):
        self.project_path = project_path
        self.file_path = None

        self._client: lc.LeanLSPClient | None = None
        self._sfc: lc.SingleFileClient | None = None
        self.history: None = None
        self.full_text: None = None
    
    @property
    def client(self) -> lc.LeanLSPClient:
        if self._client is None:
            raise RuntimeError(f"Session not active, please use with block or open method")
        return self._client

    @property
    def sfc(self) -> lc.SingleFileClient:
        if self._sfc is None:
            raise RuntimeError(f"Session not active, please use with block or open method")
        return self._sfc


    def open(self):
        self.file_path = get_temp_file(self.project_path)
        self._client = lc.LeanLSPClient(self.project_path)
        self._sfc = self.client.create_file_client(os.path.relpath(self.file_path, self.project_path))
        self.sfc.open_file()
        return self
    
    def close(self):
        if self.client:
            self.client.close()
        if self.file_path is not None:
            clear_temp_file(self.project_path,self.file_path)
            
    
    def __enter__(self):
        return self.open()

    def __exit__(self, exc_type, exc_val, exc_tb): # pyright: ignore[reportMissingParameterType, reportUnknownParameterType]
        self.close()

    def check_code(self, full_text: str) -> Tuple[List[str],List[Dict[str,Any]]]:
        self.sfc.update_file_content(full_text)
        
        line_num = full_text.count('\n')
        col_num = 0

        if g := cast(Dict[str,Any] | None, self.sfc.get_goal(line_num,col_num)): # pyright: ignore[reportUnknownMemberType]
            goals = cast(List[str],g['goals'])
        else:
            goals = []
        
        # Check diagnostics (errors)
        diagnostics = self.sfc.get_diagnostics()
        #print(diagnostics)
        if diagnostics.success:
            # print(diagnostics)
            # I believe this means no errors and no goals, apparently anywhere in the file
            return (goals,diagnostics.diagnostics)
        # print('PAST THE IF')
        diags = diagnostics.diagnostics # pyright: ignore[reportUnknownVariableType, reportUnknownMemberType]
        real_diags = []
        # pour through the stuff
        please_exit = False
        for diag in diags: # pyright: ignore[reportUnknownVariableType]
            message = cast(str,diag['message'])
            severity = cast(int,diag['severity'])
            unsolved_goal = 'leanTags' in diag and diag['leanTags'][0] == 1
            
            if unsolved_goal:
                continue
            if message.startswith('unexpected end of input'):
                continue
            if severity != 1:
                print('[!] Lean gave a warning')
                real_diags.append(diag)
                continue
            please_exit = True
            
            print(f'[!] Lean error\n{message}')
            real_diags.append(diag)
        
        if please_exit:
            raise Exception('Lean gave some errors, look above traceback')

        return (goals,real_diags) # pyright: ignore[reportUnknownVariableType]

def main():
    history: List[str] = []

    with LeanLspRepl(".") as repl:
        print('repl tester, exit exits and undo removes the last entered command\n')

        while True:
            cmd = input("lean> ")
            if cmd == "exit": break
            if cmd == "undo":
                if len(history) > 2:
                    history.pop()

            repl.check_code('\n'.join(history))



if __name__ == "__main__":
    main()
