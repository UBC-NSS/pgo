# MPCal Pygments

Pygments plugin for MPCal.

## Install

Run the following commands in the `pygments` directory:
```shell
pip install -r requirements.txt
sudo python3 setup.py develop
```

## Lexers

There are two available lexers:

* `mpcal`: 
  For highlighting MPCal code blocks.
* `tla+`:
  TLA+ highlighting that supports PlusCal and MPCal languages in the comments.

## Usage

You can use this plugin with command line. For example, output an HTML file, `output.html`, from an 
input TLA file, `/path/to/input.tla`:
```shell
pygmentize -f html -O full -o output.html /path/to/input.tla
```

For syntax highlighting inside Latex docuemtns, we use [minted](https://ctan.org/pkg/minted?lang=en) package. For more
information see the provided [example](latex/main.tex).