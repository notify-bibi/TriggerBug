import copy
import logging
import claripy
import _io

l = logging.getLogger(name=__name__)


class File_System(MEMORY_0BJECT):
    def __init__(self, state, father_state):
        self.state = state
        self.f_state = father_state
        if hasattr(father_state, 'file_system'):
            MEMORY_0BJECT.__init__(self, father_state.file_system)
        else:
            MEMORY_0BJECT.__init__(self, None)

    def __getitem__(self, item):
        now_obj = self
        while item not in now_obj.less_mem:
            now_obj = now_obj.f_obj
            if not now_obj:
                return False
        return now_obj.less_mem[item]

    def sync_file_range(self, **kwargs):
        oflag, flag = calc_flag(kwargs['flags'])
        l.info('filename:%s oflag: %s flag: %s %d', kwargs['filename'], oflag, flag, kwargs['flags'])
        if 'r' in flag:
            return self.__open_read(kwargs['filename'], oflag, flag)
        elif 'w' in flag:
            if '+' in flag:
                return self.__open_write(kwargs['filename'], True, oflag, flag)
            else:
                return self.__open_write(kwargs['filename'], False, oflag, flag)
        elif 'a' in flag:
            if '+' in flag:
                return self.__open_write(kwargs['filename'], True, oflag, flag, is_append=True)
            else:
                return self.__open_write(kwargs['filename'], False, oflag, flag, is_append=True)

    def __open_read(self, filename, oflag, flag):
        file_obj = self[filename]
        if not file_obj:
            return -err_codes['ENFILE']
        des = self.state.des_manager.register_obj(des_file(file_obj, oflag=oflag, flag=flag))
        return des

    def __open_write(self, filename, new, oflag, flag, is_append=False):
        file_obj = self[filename]
        if file_obj:
            if filename in self.less_mem:
                if not is_append:
                    file_obj.restore()
                des = self.state.des_manager.register_obj(des_file(file_obj, oflag=oflag, flag=flag, is_append=True))
                return des
            else:
                file = None
                if is_append:
                    file = copy.deepcopy(file_obj)
                else:
                    file = Symbolic_File(filename)
                des = self.state.des_manager.register_obj(des_file(file, oflag=oflag, flag=flag, is_append=False))
                return des
        else:
            if not new:
                return -err_codes['ENFILE']
            file_obj = Symbolic_File(filename)
            des = self.state.des_manager.register_obj(des_file(file_obj, oflag=oflag, flag=flag))
            return des

    def close(self, state):
        description = state.reg_r('rdi').args[0]
        des_file = self.state.des_manager[description]
        self.less_mem[des_file.file_obj.filename] = des_file.file_obj
        if description in self.state.des_manager.less_mem:
            self.state.des_manager.less_mem.pop(description)
        else:
            self.state.des_manager.less_mem[description] = False
        return 1

    def append_symbolic_file(self, filename, data):
        if isinstance(data, _io.BufferedReader):
            tmp = data.read()
            data.close()
            data = [_ for _ in tmp]
        self.less_mem[filename] = Symbolic_File(filename, data=data)


class des_file():
    def __init__(self, symbolic_file, **kwargs):
        self.file_obj = symbolic_file
        self.w_point = 0
        self.r_point = 0
        self.oflag = kwargs['oflag']
        self.flag = kwargs['flag']
        if 'is_append' in kwargs:
            if kwargs['is_append']: self.w_point = symbolic_file.getEnd()

    def read(self, state):
        rsi = state.reg_r('rsi').args[0]
        rdx = state.reg_r('rdx').args[0]
        if len(self.file_obj.mem) - self.r_point - rdx < 0:
            rdx = len(self.file_obj.mem) - self.r_point
        self.r_point += rdx
        state.mem_w(rsi, [_ for _ in self.file_obj.mem[self.r_point - rdx:self.r_point]])
        return rdx

    def write(self, state):
        rsi = state.reg_r('rsi').args[0]
        rdx = state.reg_r('rdx').args[0]
        value = state.mem_r(rsi, rdx).chop(8)
        for v in value:
            self.file_obj.mem.append(v)
        self.w_point += len(value)
        return rdx


class Symbolic_File():
    def __init__(self, filename, **kwargs):
        self.filename = filename
        if 'data' in kwargs:
            self.mem = [claripy.BVV(_, 8) for _ in kwargs['data']]
        else:
            self.mem = []

    def restore(self):
        self.mem = []

    def __str__(self):
        s = '\n'
        for index, value in enumerate(self.mem):
            if value.symbolic:
                s += '\033[1;31m' + str(value) + '\033[0m'
            else:
                s += '\033[1;32m' + chr(value.args[0]) + '\033[0m'
            if not (index + 1) % 32:
                s += '\n'
        s += '\n'
        for index, value in enumerate(self.mem):
            if value.symbolic:
                s += '\033[1;31m' + str(value) + '\033[0m '
            else:
                s += '\033[1;32m%2x' % value.args[0] + '\033[0m '
            if not (index + 1) % 32:
                s += '\n'
        return 'size:%x %s' % (len(self.mem), s)
