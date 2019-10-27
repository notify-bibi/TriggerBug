from enum import Enum


class Struct_stat_win32(Enum):
    st_dev = 0x0
    st_ino = 0x4
    st_mode = 0x6
    st_nlink = 0x8
    st_uid = 0xa
    st_gid = 0xc
    st_rdev = 0x10
    st_size = 0x14
    st_atime = 0x18
    st_mtime = 0x20
    st_ctime = 0x28


class Struct_stat_win64(Enum):
    st_dev = 0x0
    st_ino = 0x4
    st_mode = 0x6
    st_nlink = 0x8
    st_uid = 0xa
    st_gid = 0xc
    st_rdev = 0x10
    st_size = 0x14
    st_atime = 0x18
    st_mtime = 0x20
    st_ctime = 0x28


class Struct_stat_linux64(Enum):
    st_dev = 0x0
    st_ino = 0x8
    st_mode = 0x18
    st_nlink = 0x10
    st_uid = 0x1c
    st_gid = 0x20
    st_rdev = 0x28
    st_size = 0x30
    st_atime = 0x48
    st_mtime = 0x58
    st_ctime = 0x68


class Struct_stat_linux32(Enum):
    st_dev = 0x0
    st_ino = 0xc
    st_mode = 0x10
    st_nlink = 0x14
    st_uid = 0x18
    st_gid = 0x1c
    st_rdev = 0x20
    st_size = 0x2c
    st_atime = 0x38
    st_mtime = 0x40
    st_ctime = 0x48
