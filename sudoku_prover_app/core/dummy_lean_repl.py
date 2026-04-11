
from typing import Any, Dict, List, Tuple




class LeanLspRepl:
    def __init__(self, project_path: str):
        pass
    def open(self):
        return self
    
    def close(self):
        pass
            
    
    def __enter__(self):
        return self.open()

    def __exit__(self, exc_type, exc_val, exc_tb): # pyright: ignore[reportMissingParameterType, reportUnknownParameterType]
        self.close()

    def check_code(self, full_text: str) -> Tuple[List[str],List[Dict[str,Any]]]:
        print(full_text)
        print('I am dummy')
        return ([],[])
