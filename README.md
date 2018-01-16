# Expander #

*Expander* is a flexible multi-purpose workbench for interactive term rewriting, graph transformation, theorem proving, constraint solving, flow graph analysis and other procedures that build up proofs or computation sequences.

## Dependencies ##

Before compiling and installing *Expander* the following tools are needed:
* stack (tested with version 1.0.0)
* Gtk+3 (tested with version 3.18.6)

### Stack ###
Follow the installation guide [here](http://docs.haskellstack.org/en/stable/install_and_upgrade).


### Gtk+3 ###

Official download page: [www.gtk.org/download](http://www.gtk.org/download/index.php)

**Linux**
Most Linux distributions already have Gtk+ installed. Often development packages are needed. Visit official download page for more information. For Debian/Ubuntu:
```
$ apt install libgtk-3-dev
```

**Mac**
The [official download page](https://wiki.gnome.org/Projects/GTK+/OSX/Building) recommends to use jhbuild. [Homebrew](http://brew.sh/) is also known as a good alternative.
```
$ brew install gtk+3
$ export PKG_CONFIG_PATH=/usr/local/lib/pkgconfig
```
The last command is needed everytime the Expander3 package is build.

**Windows**
Needs stack to be installed.
```
stack setup
stack exec -- pacman --needed -Sy bash pacman pacman-mirrors msys2-runtime msys2-runtime-devel
stack exec -- pacman -Syu
stack exec -- pacman -Syuu
stack exec -- pacman -S pkg-config mingw-w64-x86_64-gtk3 mingw-w64-x86_64-toolchain base-devel git
```
## Installation ##
Install expander with:
```
git clone git@github.com:jokusi/expander.git
cd expander-3.0.0.0
stack setup
stack install gtk2hs-buildtools
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

## Important Folder ##

### src ###
Contains the source code.

### app ###
Main function for expander and hilbs executable.

### data/style ###
Files for layout and design.


