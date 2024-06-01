## Curl

Got version `https://github.com/curl/curl/releases/tag/curl-8_7_1`.

```sh
$ CC=wllvm CFLAGS="-O0 -fno-discard-value-names" ./configure --with-openssl
$ make
$ extract-bc -o bench.bc src/.libs/curl
```

## Cpython

Got version `https://github.com/python/cpython/releases/tag/v3.13.0b1`

```sh
$ CC=wllvm CFLAGS="-O0 -fno-discard-value-names" ./configure
$ make
$ extract-bc -o bench.bc ./python
```

## Emacs

Got version `https://github.com/emacs-mirror/emacs/releases/tag/emacs-29.3`.

```sh
$ CC=wllvm CFLAGS="-O0 -fno-discard-value-names" ./configure --without-x
$ cd src
$ make
$ extract-bc -o ../bench.bc emacs
```

## Htop

Got version `https://github.com/htop-dev/htop/releases/tag/3.3.0`.

```sh
$ CC=wllvm CFLAGS="-O0 -fno-discard-value-names" ./configure
$ make
$ extract-bc -o bench.bc htop
```

## Make

Got version `https://ftp.gnu.org/gnu/make/make-4.4.1.tar.gz`.

```sh
$ CC=wllvm CFLAGS="-O0 -fno-discard-value-names" ./configure
$ ./build.sh
$ extract-bc -o bench.bc make
```

## Vim

Got version `https://github.com/vim/vim/releases/tag/v9.1.0386`.

```sh
$ CC=wllvm CFLAGS="-O0 -fno-discard-value-names" ./configure
$ make
$ extract-bc -o bench.bc src/vim
```
