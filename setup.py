import setuptools
setuptools.setup(
    name='vhdllint',
    version='1.0',
    scripts=['./vhdllint.py'],
    author='Me',
    description='VHDL Linter',
    install_requires=[
        'setuptools',
    ],
    python_requires='>=3.5',
    entry_points={
        'console_scripts': [
            'vhdllint = vhdllint:main'
        ]
    }
)
