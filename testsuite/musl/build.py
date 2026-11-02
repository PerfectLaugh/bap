#!/usr/bin/env python3
# Builds a program of testsuite/src against a static musl, from the sources of it that zig has, with clang and ld.lld, for what zig itself doesn't run on:
#   build.py TARGET SOURCE OUTPUT
# What it compiles of musl stays in $BAP_MUSL_BUILD, or else under the temporary directory, as it takes a while.
import os,subprocess,sys,glob,tempfile,concurrent.futures as cf
Z="/usr/lib/zig/libc"; M=Z+"/musl"; I=Z+"/include"
T={ "x86_64":("x86_64","x86_64-linux-musl","x86_64",[]),
    "aarch64":("aarch64","aarch64-linux-musl","aarch64",[]),
    "riscv64":("riscv64","riscv64-linux-musl","riscv64",["-march=rv64gc","-mabi=lp64d"]),
    "riscv32":("riscv32","riscv32-linux-musl","riscv32",["-march=rv32gc","-mabi=ilp32d"]),
    "arm":("arm","arm-linux-musleabihf","arm",["-march=armv7-a","-mfloat-abi=hard","-mfpu=vfpv3-d16"]),
    "thumb":("arm","arm-linux-musleabihf","arm",["-march=armv7-a","-mthumb","-mfloat-abi=hard","-mfpu=vfpv3-d16"]),
    "i686":("i386","i686-linux-musl","x86",[]),
    "mips":("mips","mips-linux-musl","mips",["-mips32r2"]),
    "mipsel":("mips","mipsel-linux-musl","mips",["-mips32r2"]),
    "mips64":("mips64","mips64-linux-muslabi64","mips64",["-mips64r2"]),
    "mips64el":("mips64","mips64el-linux-muslabi64","mips64",["-mips64r2"]),
    "powerpc":("powerpc","powerpc-linux-musl","powerpc",[]),
    "powerpc64":("powerpc64","powerpc64-linux-musl","powerpc64",["-mabi=elfv2"]),
    "powerpc64le":("powerpc64","powerpc64le-linux-musl","powerpc64",["-mabi=elfv2"]),
}
name=sys.argv[1]; src=sys.argv[2]; out=sys.argv[3]
A,triple,inc,extra=T[name]
B=os.path.join(os.environ.get("BAP_MUSL_BUILD",os.path.join(tempfile.gettempdir(),"bap-musl")),name); os.makedirs(B,exist_ok=True)
open(B+"/version.h","w").write('#define VERSION "1.2.5"\n')
pic="-fPIC" if name.startswith("mips") and "64" not in name else "-fno-pic"
flags=["--target="+triple,"-std=c99","-nostdinc","-ffreestanding","-fno-builtin","-O1",pic,"-D_XOPEN_SOURCE=700","-w","-fno-stack-protector","-fomit-frame-pointer",
  "-I"+M+"/arch/"+A,"-I"+M+"/arch/generic","-I"+B,"-I"+M+"/src/include","-I"+M+"/src/internal","-I"+I+"/"+inc+"-linux-musl","-I"+I+"/generic-musl"]+extra
if name=="i686": flags+=["-I"+I+"/x86-linux-musl"]
dirs=[d for d in glob.glob(M+"/src/*") if os.path.basename(d) not in("math","complex","ldso","network","fenv","regex","search","locale","legacy","conf","crypt","aio","ipc","linux","passwd","prng","temp","ctype","multibyte","dirent","select","sched_","stat","termios","fcntl_","include","internal_")]
objs=[]; jobs=[]
for d in dirs+[M+"/src/internal"]:
    base={}
    for f in glob.glob(d+"/*.c"): base[os.path.basename(f).rsplit(".",1)[0]]=f
    for f in glob.glob(d+"/"+A+"/*.[csS]"): base[os.path.basename(f).rsplit(".",1)[0]]=f
    for k,f in base.items():
        o=f"{B}/{os.path.basename(d)}_{k}.o"; objs.append(o); jobs.append((f,o))
def cc(j):
    f,o=j
    if os.path.exists(o): return None
    r=subprocess.run(["clang"]+flags+["-c",f,"-o",o],capture_output=True,text=True)
    if r.returncode: return (f,r.stderr[-300:])
with cf.ThreadPoolExecutor(32) as e: errs=[x for x in e.map(cc,jobs) if x]
objs=[o for o in objs if os.path.exists(o)]
crt=[]
for n,src_ in (("crt1",M+"/crt/crt1.c"),("crti",M+"/crt/"+A+"/crti.s"),("crtn",M+"/crt/"+A+"/crtn.s")):
    o=f"{B}/{n}.o"; subprocess.run(["clang"]+flags+["-c",src_,"-o",o],capture_output=True); crt.append(o)
lib=B+"/libc.a"
if os.path.exists(lib): os.remove(lib)
subprocess.run(["llvm-ar" if subprocess.run(["which","llvm-ar"],capture_output=True).returncode==0 else "ar","rcs",lib]+objs,check=True)
b=B+"/builtins.o"
subprocess.run(["clang"]+flags+["-c",os.path.dirname(os.path.abspath(__file__))+"/builtins.c","-o",b],check=True)
t=B+"/test.o"
r=subprocess.run(["clang",f"--target={triple}","-nostdinc","-fno-builtin","-O1",pic,"-w","-fno-stack-protector","-I"+I+"/"+inc+"-linux-musl","-I"+I+"/generic-musl"]+extra+["-c",src,"-o",t],capture_output=True,text=True)
if r.returncode: print("test compile:",r.stderr[-600:]); sys.exit(1)
r=subprocess.run(["ld.lld","-static","--gc-sections","-z","noexecstack","-o",out]+[c for c in crt[:2] if os.path.exists(c)]+[t,lib,b]+[c for c in crt[2:] if os.path.exists(c)],capture_output=True,text=True)
if r.returncode: print("link:",r.stderr[:900]); sys.exit(1)
print("built",out)
