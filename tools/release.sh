#!/bin/sh

set -e

sudo apt-get update
sudo apt-get install alien autoconf llvm-dev --yes

BAP_VERSION=$1
echo "version is $BAP_VERSION"


GITHUB=https://github.com/BinaryAnalysisPlatform/
SOURCE=$GITHUB/bap
BINDINGS=$GITHUB/bap-bindings
PREFIX=/usr/local
ARCH=$(dpkg-architecture -qDEB_BUILD_ARCH)
CONFDIR=$PREFIX/etc/bap

eval $(opam env)
echo OCaml is at $(which ocaml)
echo "Looking in the dev-repo for the current list of dependencies"
opam pin add bap --dev-repo --yes -n
echo "Installing the dependencies"
opam install --yes --confirm-level=unsafe-yes --deps-only bap
echo "Installed dependencies. Cleaning up..."
opam pin remove bap

echo "Cloning a fresh repo"
[ -d bap-repo ] || git clone --recursive $SOURCE bap-repo
cd bap-repo
LLVM_CONFIG=$(command -v llvm-config)
LLVM_VERSION=$($LLVM_CONFIG --version)

# this is a bit recursive...
SIGURL=https://github.com/BinaryAnalysisPlatform/bap/releases/download/v2.4.0-alpha
echo BAP version is $BAP_VERSION
echo LLVM is $LLVM_VERSION

ocaml tools/configure.ml \
      --with-llvm-version=$LLVM_VERSION \
      --with-llvm-config=$LLVM_CONFIG \
      --prefix=$PREFIX \
      --sysconfdir=$CONFDIR

dune build --release --pkg=disabled
cd ..

echo "Packing a bap debian package"

sudo rm -rf bap

mkdir -p bap/bap_$BAP_VERSION/DEBIAN

STAGE=$(pwd)/bap/bap_$BAP_VERSION
SHARED=$STAGE/$PREFIX/share
DEBIAN=$STAGE/DEBIAN

SIGDIR=$SHARED/bap/signatures/

(cd bap-repo && dune install --release --pkg=disabled --prefix=$PREFIX --destdir=$STAGE)

echo "Installing Byteweight signatures"
mkdir -p $SIGDIR
curl -L $SIGURL/sigs.zip > $SIGDIR/byteweight.zip

cat > $DEBIAN/control <<EOF
Package: bap
Architecture: $ARCH
Maintainer: Ivan Gotovchits
Depends: libgmp10, zlib1g, libstdc++6, libtinfo6
Priority: optional
Version: $BAP_VERSION
Description: Binary Analysis Platform
EOF

sudo chown -R root:root bap/bap_$BAP_VERSION
dpkg-deb --build bap/bap_$BAP_VERSION

echo "now building the bindings"

opam install ctypes ctypes-foreign --yes

[ -d bap-bindings ] || git clone $BINDINGS bap-bindings


cd bap-bindings
git pull
autoconf
./configure
make
cd ..


echo "Now packing libbap.deb"
LIBDIR=bap/libbap_$BAP_VERSION/$PREFIX/lib
DEBIAN=bap/libbap_$BAP_VERSION/DEBIAN

mkdir -p $LIBDIR $DEBIAN


cp bap-bindings/_build/bap/libbap.so $LIBDIR/libbap.so.$BAP_VERSION


cat > $DEBIAN/control <<EOF
Package: libbap
Architecture: $ARCH
Maintainer: Ivan Gotovchits
Depends: libgmp10, zlib1g, libstdc++6, libffi8, libtinfo6
Priority: optional
Version: $BAP_VERSION
Description: Binary Analysis Platform C Library
EOF

cat > $DEBIAN/postinst <<EOF
#!/bin/sh
ldconfig
EOF

cat > $DEBIAN/postrm <<EOF
#!/bin/sh
ldconfig
EOF

chmod a+x $DEBIAN/postinst
chmod a+x $DEBIAN/postrm
sudo chown -R root:root bap/libbap_$BAP_VERSION
dpkg-deb --build bap/libbap_$BAP_VERSION

echo "Now packing libbap-dev"
HDRDIR=bap/libbap-dev_$BAP_VERSION/$PREFIX/include
DEBIAN=bap/libbap-dev_$BAP_VERSION/DEBIAN

mkdir -p $DEBIAN $HDRDIR
cp bap-bindings/_build/bap/generated/bap.h $HDRDIR

cat > $DEBIAN/control <<EOF
Package: libbap-dev
Architecture: $ARCH
Maintainer: Ivan Gotovchits
Depends: libbap
Priority: optional
Version: $BAP_VERSION
Description: Binary Analysis Platform C Library
EOF

cat > $DEBIAN/postinst <<EOF
#!/bin/sh
ln -sf $PREFIX/lib/libbap.so.$BAP_VERSION $PREFIX/lib/libbap.so
ldconfig
EOF

cat > $DEBIAN/postrm <<EOF
#!/bin/sh
ldconfig
EOF

chmod a+x $DEBIAN/postinst
chmod a+x $DEBIAN/postrm
sudo chown -R root:root bap/libbap-dev_$BAP_VERSION
dpkg-deb --build bap/libbap-dev_$BAP_VERSION

cd bap/
curl -L $SIGURL/sigs.zip > sigs.zip
curl -L $SIGURL/sigs.tar.gz > sigs.tar.gz

for pkg in bap libbap libbap-dev; do
    deb=$pkg\_$BAP_VERSION
    dir=$pkg-$BAP_VERSION
    sudo alien --to-rpm -g $deb.deb
    cd $dir
    spec=$(mktemp)
    awk '/%dir.*bap/ {print} /%dir/ {next} {print}' $pkg-$BAP_VERSION-2.spec > $spec
    sudo cp $spec $pkg-$BAP_VERSION-2.spec
    sudo rpmbuild -bb $pkg-$BAP_VERSION-2.spec --buildroot=$(pwd)
    echo "trying to run alien"
    echo alien --to-tgz $deb.deb
    cd ..
    ls -l
    alien --to-tgz $deb.deb
    sudo rm -rf $dir
done
