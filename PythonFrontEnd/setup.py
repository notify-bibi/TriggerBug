#!/usr/bin/env python
# coding=utf-8

from setuptools import find_packages
from setuptools import setup
from distutils.command.build import build as _build
from distutils.command.clean import clean as _clean
import os,shutil
packages = find_packages()
print(packages)

ROOT_DIR = os.path.abspath(os.path.dirname(__file__))



setup(
    name="TriggerBug", 
    version="2.0",
    author="wu xing chuan",
    python_requires='>=3.0',

    install_requires=[
        'archinfo>=8.19.0.0',
        'setuptools>=16.0',
		'capstone>=4.0.0',
		'keystone'
    ],
    packages=packages,
	zip_safe=False,
	package_data={
        'TriggerBug': ['libs/*']
    }
)