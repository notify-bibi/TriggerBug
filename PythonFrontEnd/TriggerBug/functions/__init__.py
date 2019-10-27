import os
import logging


try:
    import _pickle as pickle
except:
    import pickle
import hashlib

log = logging.getLogger(name=__name__)

file_define_c = {
    0: 'O_RDONLY',
    1: 'O_WRONLY',
    2: 'O_RDWR',
    8: 'O_APPEND',
    0x100: 'O_CREAT',
    0x200: 'O_TRUNC',
    0x400: 'O_EXCL',
    0x4000: 'O_TEXT',
    0x8000: 'O_BINARY',
    0x40: 'O_TEMPORARY',
    0x80: 'O_NOINHERIT',
    0x20: 'O_SEQUENTIAL',
    0x10: 'O_RANDOM'
}

err_codes = {
    'EPERM': 1,
    'ENOENT': 2,
    'ESRCH': 3,
    'EINTR': 4,
    'EIO': 5,
    'ENXIO': 6,
    'E2BIG': 7,
    'ENOEXEC': 8,
    'EBADF': 9,
    'ECHILD': 10,
    'EAGAIN': 11,
    'ENOMEM': 12,
    'EACCES': 13,
    'EFAULT': 14,
    'EBUSY': 16,
    'EEXIST': 17,
    'EXDEV': 18,
    'ENODEV': 19,
    'ENOTDIR': 20,
    'EISDIR': 21,
    'ENFILE': 23,
    'EMFILE': 24,
    'ENOTTY': 25,
    'EFBIG': 27,
    'ENOSPC': 28,
    'ESPIPE': 29,
    'EROFS': 30,
    'EMLINK': 31,
    'EPIPE': 32,
    'EDOM': 33,
    'EDEADLK': 36,
    'ENAMETOOLONG': 38,
    'ENOLCK': 39,
    'ENOSYS': 40,
    'ENOTEMPTY': 41
}

def pickle_read(file_name, **kwargs):
    if not os.path.exists(file_name):
        return False
    pickle_file = open(file_name, 'rb')
    my_list = pickle.load(pickle_file, **kwargs)
    pickle_file.close()
    return my_list


def pickle_write(file_name, data, **kwargs):
    pickle_file = open(file_name, 'wb')
    pickle.dump(data, pickle_file, **kwargs)
    pickle_file.close()


def calcMD5(filepath):
    try:
        with open(filepath, 'rb') as f:
            md5obj = hashlib.md5()
            md5obj.update(f.read())
            hash = md5obj.hexdigest()
            return True, hash
    except Exception as e:
        return False, e


def rIterator(kwargs):
    n = len(kwargs)
    while n > 0:
        n -= 1
        yield kwargs[n]
    raise StopIteration()


def zIterator(kwargs):
    n = len(kwargs)
    i = 0
    while i < n:
        yield kwargs[i]
        i += 1
    raise StopIteration()


def mk_symbolic_address_return(address_symbolic, tuple, mem_tuple, depth):
    if len(tuple) - 1 == depth:
        return mem_tuple[depth]
    else:
        return claripy.If(address_symbolic == tuple[depth], mem_tuple[depth],
                          mk_symbolic_address_return(address_symbolic, tuple, mem_tuple, depth + 1))


def get_symbolic(symbolic, symbolic_obj):
    for var in symbolic.args:
        if type(var) == claripy.ast.bv.BV:
            if var.symbolic:
                if var.depth == 1:
                    symbolic_obj.symbolics.append(var)
                else:
                    get_symbolic(var, symbolic_obj)


class Symbolics():
    def __init__(self):
        self.symbolics = []

def bv2it(bv):
    if 8 == bv.length:
        yield bv
        raise StopIteration()
    for n in range(0, bv.length, 8):
        yield bv[n + 7:n]


def align(a, size):
    return a & ~(size - 1)


def ShowRegs(state):
    log.info('rax%18x', state.reg_r('rax'))
    log.info('rbx%18x', state.reg_r('rbx'))
    log.info('rcx%18x', state.reg_r('rcx'))
    log.info('rdx%18x', state.reg_r('rdx'))

    log.info('rsi%18x', state.reg_r('rsi'))
    log.info('rdi%18x', state.reg_r('rdi'))
    log.info('rbp%18x', state.reg_r('rbp'))
    log.info('rsp%18x', state.reg_r('rsp'))
    log.info('rip%18x', state.reg_r('rip'))

    log.info('r8 %18x', state.reg_r('r8'))
    log.info('r9 %18x', state.reg_r('r9'))
    log.info('r10%18x', state.reg_r('r10'))
    log.info('r11%18x', state.reg_r('r11'))
    log.info('r12%18x', state.reg_r('r12'))
    log.info('r13%18x', state.reg_r('r13'))
    log.info('r14%18x', state.reg_r('r14'))
    log.info('r15%18x', state.reg_r('r15'))

def calc_flag(flags):
    length = len(bin(flags)) - 2
    s = ''
    p = ''
    for l in range(length):
        mask = pow(2, l)
        bit = mask & flags
        if bit:
            s += file_define_c[pow(2, l)] + '|'
        elif l == 0:
            s = 'O_RDONLY|'
    s = s[:-1]
    if file_define_c[0] in s:  # O_RDONLY
        p = 'r'
        if file_define_c[0x8000] in s:  # O_BINARY
            p += 'b'
        elif file_define_c[0x4000] in s:  # O_TEXT
            p += ''

    elif file_define_c[1] in s:  # O_WRONLY
        p = 'w'
        if file_define_c[0x8000] in s:  # O_BINARY
            p += 'b'
        elif file_define_c[0x4000] in s:  # O_TEXT
            p += ''
        if file_define_c[0x100] in s:  # O_CREAT
            p += '+'
        elif file_define_c[0x40] in s:
            p += '+'
    elif file_define_c[8] in s:  # O_APPEND
        p = 'a'
        if file_define_c[0x8000] in s:  # O_BINARY
            p += 'b'
        elif file_define_c[0x4000] in s:  # O_TEXT
            p += ''
        if file_define_c[0x100] in s:  # O_CREAT
            p += '+'
        elif file_define_c[0x40] in s:
            p += '+'
    return s, p