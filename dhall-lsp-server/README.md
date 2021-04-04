# Dhall language support in VSCode/ium

The Dhall language integration consists of the following parts:
- The VSCode/ium plugin "Dhall Language Support" *([vscode-language-dhall](https://github.com/PanAeon/vscode-language-dhall))* adds syntax highlighting for Dhall files.
- The VSCode/ium plugin "Dhall LSP Server" *([vscode-dhall-lsp-server](https://github.com/PanAeon/vscode-dhall-lsp-server))* implements the LSP client &ndash; yes, there is a naming issue here &ndash; that communicates with the backend via the [LSP protocol](https://microsoft.github.io/language-server-protocol/specification) to provide advanced language features like error diagnostics or type information, etc.
- [*dhall-lsp-server*](https://github.com/dhall-lang/dhall-haskell/tree/master/dhall-lsp-server), which is part of the [*dhall-haskell*](https://github.com/dhall-lang/dhall-haskell) project, implements the actual LSP server (i.e. the backend) that implements those language features in an editor agnostic way, though at the moment only a VSCode/ium frontend exists.

# Installation

The "official" releases can be installed as follows:

- **vscode-language-dhall** should be installed directly from VSCode/ium via the extensions marketplace.
- **vscode-dhall-lsp-server** can also be installed directly from the marketplace.
- **dhall-lsp-server** can be installed from hackage with `cabal install dhall-lsp-server`. See the
[`dhall-haskell` `README`](https://github.com/dhall-lang/dhall-haskell/blob/master/README.md) for pre-built binaries, as well as comprehensive installation and development instructions using *cabal*, *stack* or *nix*.

## Installing the latest development versions

**Note&nbsp;** The versions of *vscode-dhall-lsp-server* and *dhall-lsp-server* need not necessarily match: an older client version will simply not expose all commands available in the backend, while an older server might not implement all commands exposed in the UI.

**vscode-dhall-lsp-server**
1. You need to have *npm* installed (e.g. using your favourite package manager).
2. Install the *typescript* compiler with `npm install -g typescript`. I recommend running `npm config set prefix '~/.local'` first to have npm install the executable in `~/.local/bin`; this avoids having to use *sudo* and polluting the rest of the system.
2. Check out a copy of the vscode-dhall-lsp-server repository into the VSCode/ium extensions folder
   ```
   git clone git@github.com:PanAeon/vscode-dhall-lsp-server.git ~/.vscode-oss/extensions/vscode-dhall-lsp-server
   ```
   (replace `~/.vscode-oss/` with `~/.vscode/` if you use VSCode instead of VSCodium).
3. Run the remaining commands in the checked-out directory
   ```
   cd ~/.vscode-oss/extensions/vscode-dhall-lsp-server
   ```
4. Run `npm install` to fetch all library dependencies.
5. Run `npm run compile` to compile the typescript code to javascript.
6. Start (restart) VSCode/ium.

**dhall-lsp-server&nbsp;**
For detailed instructions as well as instructions using cabal or nix, see [`dhall-haskell` - `README`](https://github.com/dhall-lang/dhall-haskell/blob/master/README.md). To install dhall-lsp-server using *stack*:
1. Clone `git@github.com:dhall-lang/dhall-haskell.git`.
2. Inside the checked out repository run `stack install dhall-lsp-server`.


# Usage / Features

- **Diagnostics&nbsp;**
Every time you save a Dhall file it is parsed and typechecked, and any errors are marked. You can hover over the offending code to see the error message; to see a detailed explanation in the case of type errors, click the *Explain* link in the hover box.

- **Clickable imports&nbsp;**
As long as the file parses successfully, all (local file and remote) imports will be underlined and clickable.

- **Type on hover&nbsp;**
You can hover over any part of the code and it will tell you the type of the subexpression at that point &ndash; if you highlight an identifier you see its type; if you highlight the `->` in a function you will see the type of the entire function. This feature only works if the code passes the typechecker!

- **Code completion&nbsp;**
As you type you will be offered completions for:
  - environment variables
  - local imports
  - identifiers in scope (as well as built-ins)
  - record projections from 'easy-to-parse' records (of the form `ident1.ident2`[`.ident3...`])
  - union constructors from 'easy-to-parse' unions

  This is the only feature that works even when the file does not parse (or typecheck).

- **Formatting and Linting&nbsp;**
Right click and select "Format Document" to run the file through the Dhall formatter. The command "Lint and Format" can be selected via the *Command Palette* (Ctrl+Shift+P); this will run the linter over the file, removing unused let bindings and formatting the result.

- **Annotate lets&nbsp;**
Right-click the bound identifier in a `let` binding and select "Annotate Let binding with its type" to do exactly that.

- **Freeze imports&nbsp;**
Right-click an import statement and select "Freeze (refreeze) import" to add (or update) a semantic hash annotation to the import. You can also select "Freeze (refreeze) all imports" from the *Command Palette* to freeze all imports at once.

  Note that this feature behaves slightly differently from the `dhall freeze` command in that the hash annotations are inserted without re-formatting the rest of the code!

# Developer notes

**dhall-lsp-server&nbsp;**
See [`dhall-haskell` - `README`](https://github.com/dhall-lang/dhall-haskell/blob/master/README.md) for general development instructions.
- You can also build using `stack build dhall-lsp-server` and point `vscode-dhall-lsp-server.executable` in the VSCode/ium settings to the stack build directory to avoid overriding the already installed version of the LSP server.
- You can use standard `Debug.Trace`/`putStrLn` debugging; the output will show up in the "Output" panel in VSCode/ium.
- To log all LSP communication set `vscode-dhall-lsp-server.trace.server` to `verbose` in VSCode/ium.

**vscode-dhall-lsp-server**
- Instead of working in `~/vscode-oss/extensions/...` directly, you can open a clone of the git repository in VSCode/ium and use the built-in debugging capabilities for extensions: press F5 (or click the green play button in the debugging tab) to launch a new VSCode/ium window with the modified extension (potentially shadowing the installed version).
- To package a release:
  1. Make sure you have *npm* and *tsc* installed.
  2. Use `npm install -g vsce` to install the *vsce* executable.
  3. Run `vsce package` inside the git repo to package the extension, resulting in a file `vscode-dhall-lsp-server-x.x.x.vsix`.
  4. You can install the packaged extension directly by opening the `.vsix` file from within VSCod/ium.
  
**Integration tests**

The `dhall-lsp-server:tests` testsuite depends on the `dhall-lsp-server` executable. Since `stack` isn't aware of this dependency, `stack test dhall-lsp-server:tests` may use an old executable version. Run these tests with

    stack test dhall-lsp-server:tests dhall-lsp-server:dhall-lsp-server
    
to ensure that the executable is up-to-date.
