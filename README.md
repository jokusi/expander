# Expander3 #

[Expander2](https://fldit-www.cs.tu-dortmund.de/~peter/Expander2.html) is a flexible multi-purpose workbench for interactive term rewriting, graph transformation, theorem proving, constraint solving, flow graph analysis and other procedures that build up proofs or other symbolic derivations. Moreover, tailor-made interpreters display terms and formulas as two-dimensional structures ranging from trees and rooted graphs to a variety of pictorial representations such as tables, matrices, alignments, partitions and fractals.
  
Expander2 is implemented in [O'Haskell](http://fldit-www.cs.tu-dortmund.de/~peter/OhugsSurvey.html), an extension of [Haskell](http://www.haskell.org/) that admits object-oriented reactive programming and provides an interface to Tcl/Tk for GUI programming.

In Expander3, the special O'Haskell constructs are replaced by more or less equivalent "native" Haskell features and the GUI part is based on GTK+ instead of Tcl/Tk.

## Dependencies ##

For compiling and installing *Expander* the following tools are needed:
* stack
* Gtk+3

### Stack ###
Follow the installation guide [here](http://docs.haskellstack.org/en/stable/install_and_upgrade).


### Gtk+3 ###

Download with Homebrew [here](https://formulae.brew.sh/formula/gtk+3).

**Linux**

Most Linux distributions already have Gtk+ installed. Often development packages are needed. Visit official download page for more information. For Debian/Ubuntu:
```
$ apt install libgtk-3-dev
```

**Mac**

The [official download page](https://wiki.gnome.org/Projects/GTK+/OSX/Building) recommends to use [jhbuild](https://wiki.gnome.org/Projects/Jhbuild/Mac_OS) (see also [GTK for Mac OS](https://www.gtk.org/docs/installations/macos)). [Homebrew](https://formulae.brew.sh/formula/gtk+3) is a good alternative.
```
$ brew install gtk+3
$ export PKG_CONFIG_PATH=/usr/local/lib/pkgconfig
```
The last command is needed everytime the Expander3 package is build.

**Windows**
Needs stack to be installed.
```
stack setup
stack exec -- pacman -Syuu
stack exec -- pacman -S pkg-config mingw-w64-x86_64-gtk3 mingw-w64-x86_64-toolchain base-devel git
```
## Installation ##

Install expander with:
```
git clone https://github.com/jokusi/expander.git
cd expander
stack build
```

Run expander with:
```
stack exec expander
```

Update expander with:
```
git pull
stack build
```

## Important folders ##

**src**

source code

**app**

main function for expander and hilbs executables

**data/style**

files for layout and design

## Documents, pictures and videos ##

https://padawitz.de/expander3.html
