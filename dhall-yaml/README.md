# `dhall-yaml`

For installation or development instructions, see:

* [`dhall-haskell` - `README`](https://github.com/dhall-lang/dhall-haskell/blob/master/README.md)

Full documentation here:

* [`dhall-yaml` instructions](https://hackage.haskell.org/package/dhall-yaml/docs/Dhall-Yaml.html)

## Introduction

This `dhall-yaml` package provides a Dhall to YAML compiler, `dhall-to-yaml-ng`,
and a tool for deriving Dhall from YAML code: `yaml-to-dhall`.

Note that the `dhall-json` package also provides a `dhall-to-yaml` executable.
Currently, the behavior of the `dhall-to-yaml` and `dhall-to-yaml-ng`
executables should not differ much, but eventually the `dhall-to-yaml-ng`
executable should be able to support greater functionality due to using the
`HsYAML` package as an intermediate step in the transformation process.

Tutorials for the analogous JSON tools are available in the `dhall-json`
package:

* [`dhall-to-json`](https://hackage.haskell.org/package/dhall-json/docs/Dhall-JSON.html)

* [`json-to-dhall`](https://hackage.haskell.org/package/dhall-json/docs/Dhall-JSONToDhall.html)

## Example

```bash
$ dhall-to-yaml-ng <<< "{ foo = [1, 2, 3], bar = { baz = True } }" > example.yaml
$ cat example.yaml
bar:
  baz: true
foo:
- 1
- 2
- 3
$ yaml-to-dhall '{ foo : List Natural, bar : { baz : Bool } }' < example.yaml
{ bar = { baz = True }, foo = [ 1, 2, 3 ] }
```
