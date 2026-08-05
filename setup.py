import setuptools
setuptools.setup(
    name='vhdllint',
    version='1.0',
    py_modules=['vhdllint'],
    scripts=['./vhdllint.py'],
    author='Me',
    description='VHDL Linter',
    python_requires='>=3.5',
    entry_points={
        'console_scripts': [
            'vhdllint = vhdllint:main'
        ]
    }
)
