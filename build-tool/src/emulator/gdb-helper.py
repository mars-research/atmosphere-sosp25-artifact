# Reference:
# - RedLeaf Vermilion

import gdb

LOADED_BINARIES = 'aloader::debugger::LOADED_BINARIES'
LOADED_BINARIES_LEN = 'aloader::debugger::LOADED_BINARIES_LEN'
ON_BINARY_ADDED = 'aloader::debugger::on_binary_added'
ON_READY = 'aloader::debugger::on_ready'

binaries_consumed = 0

class DelayedExecute:
    def __init__(self, command: str, to_string=False) -> None:
        self.command: str = command
        self.to_string = to_string

    def __call__(self):
        gdb.execute(self.command, to_string=self.to_string)

def get_str(val):
    data_ptr = val['data_ptr']
    length = val['length']
    return data_ptr.string(length=length)

def unwrap_maybe_uninit(val):
    return val['value']['value']

def add_binary(index):
    raw_list = gdb.parse_and_eval(LOADED_BINARIES)
    binary = unwrap_maybe_uninit(raw_list[index])

    name = get_str(binary['name'])
    offset = int(binary['offset'])

    path_var = gdb.convenience_variable(f'bin_{name}')

    if path_var:
        path = path_var.string()
        gdb.execute(f'add-symbol-file {path} -o {offset:#x}', from_tty=False)
    else:
        print(f'Loaded {name} at 0x{offset:x}, but no path is known')

def dump_loaded_binaries():
    raw_list = gdb.parse_and_eval(LOADED_BINARIES)
    num_binaries = int(gdb.parse_and_eval(LOADED_BINARIES_LEN))

    for i in range(num_binaries):
        binary = unwrap_maybe_uninit(raw_list[i])
        name = get_str(binary['name'])
        offset = int(binary['offset'])

        path_var = gdb.convenience_variable(f'bin_{name}')

        if path_var:
            path = path_var.string()
            print(f'{name} @ 0x{offset:x}: {path}')
        else:
            print(f'{name} @ 0x{offset:x}: ???')

class OnBinaryLoadedBreakpoint(gdb.Breakpoint):
    def __init__(self):
        super().__init__(ON_BINARY_ADDED)

    def stop(self):
        global binaries_consumed

        num_binaries = int(gdb.parse_and_eval(LOADED_BINARIES_LEN))
        for i in range(binaries_consumed, num_binaries):
            add_binary(i)

        binaries_consumed = num_binaries

        return False

OnBinaryLoadedBreakpoint()
gdb.execute(f'break {ON_READY}')
