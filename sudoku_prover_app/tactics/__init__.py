# this registers all the tactics in the folder
# will eventually be replaced with dynamic loading based on lean imports


import pkgutil
import importlib

# This finds all submodules in the current directory (tactics/)
# and imports them, which triggers their @registry.register decorators.
for loader, module_name, is_pkg in pkgutil.iter_modules(__path__):
    # Construct the full module path
    full_module_name = f"{__name__}.{module_name}"
    importlib.import_module(full_module_name)
