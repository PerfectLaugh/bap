// What native code does with JNI, called by the host with an environment that a model serves: classes, methods with their
// arguments and results of each width, strings, objects, and the VM and its environment. Each bit of what `run` gives is one thing
// that came out as it should. The table is the one of jni.h, by index.
#include <stdint.h>
#include <stdarg.h>

typedef int32_t jint;
typedef int64_t jlong;
typedef void *jobject;
typedef void *jmethodID;
typedef void *Env;

#define TABLE(env) (*(void ***)(env))
#define FN(env, index, type) ((type)(TABLE(env)[index]))

typedef int8_t jbyte;
typedef int16_t jshort;
typedef uint16_t jchar;
typedef union { unsigned char z; jbyte b; jchar c; jshort s; jint i; jlong j; float f; double d; jobject l; } jvalue;

/* The `V` form of a call, of a `va_list` of what this is given, as a variadic function of native code passes its own on. */
static jint byList(Env env, int index, jobject target, jobject clazz, jmethodID method, ...) {
  va_list list;
  va_start(list, method);
  jint result = index >= 64 && index <= 93
    ? FN(env, index, jint (*)(Env, jobject, jobject, jmethodID, va_list))(env, target, clazz, method, list)
    : FN(env, index, jint (*)(Env, jobject, jmethodID, va_list))(env, target, method, list);
  va_end(list);
  return result;
}

__attribute__((noinline, used)) int run(Env env, jobject self) {
  int found = 0;
  if (FN(env, 4, jint (*)(Env))(env) == 0x10006) found |= 1 << 0;
  jobject thing = FN(env, 6, jobject (*)(Env, const char *))(env, "example/Thing");
  jmethodID twice = FN(env, 33, jmethodID (*)(Env, jobject, const char *, const char *))(env, thing, "twice", "(I)I");
  if (FN(env, 49, jint (*)(Env, jobject, jmethodID, ...))(env, self, twice, 21) == 42) found |= 1 << 1;
  jmethodID wide = FN(env, 33, jmethodID (*)(Env, jobject, const char *, const char *))(env, thing, "wide", "()J");
  if (FN(env, 52, jlong (*)(Env, jobject, jmethodID, ...))(env, self, wide) == 0x123456789abcdef0LL) found |= 1 << 2;
  jmethodID half = FN(env, 33, jmethodID (*)(Env, jobject, const char *, const char *))(env, thing, "half", "()D");
  if (FN(env, 58, double (*)(Env, jobject, jmethodID, ...))(env, self, half) == 2.5) found |= 1 << 3;
  jmethodID quarter = FN(env, 33, jmethodID (*)(Env, jobject, const char *, const char *))(env, thing, "quarter", "()F");
  if (FN(env, 55, float (*)(Env, jobject, jmethodID, ...))(env, self, quarter) == 1.25f) found |= 1 << 4;
  // Five arguments after the three of every call, which some systems have on the stack.
  jmethodID sum = FN(env, 113, jmethodID (*)(Env, jobject, const char *, const char *))(env, thing, "sum", "(IIIII)I");
  if (FN(env, 129, jint (*)(Env, jobject, jmethodID, ...))(env, thing, sum, 1, 2, 3, 4, 5) == 15) found |= 1 << 5;
  jobject text = FN(env, 167, jobject (*)(Env, const char *))(env, "hello");
  const char *chars = FN(env, 169, const char *(*)(Env, jobject, void *))(env, text, 0);
  if (FN(env, 168, jint (*)(Env, jobject))(env, text) == 5 && chars && chars[0] == 'h' && chars[4] == 'o') found |= 1 << 6;
  void *vm = 0;
  void *again = 0;
  if (FN(env, 219, jint (*)(Env, void **))(env, &vm) == 0 && vm &&
      ((jint (*)(void *, void **, jint))((*(void ***)vm)[6]))(vm, &again, 0x10006) == 0 && again == env)
    found |= 1 << 7;
  jobject fresh = FN(env, 27, jobject (*)(Env, jobject))(env, thing);
  jobject kind = FN(env, 31, jobject (*)(Env, jobject))(env, fresh);
  if (fresh && FN(env, 24, unsigned char (*)(Env, jobject, jobject))(env, kind, thing)) found |= 1 << 8;
  // A method of an argument of each kind, in each form of each kind of call, which says by a bit of each that it was given it: more
  // than there are registers for, a `double` and a `float` where the system has them, and what is narrower than an `int`.
  const char *mixed = "(IJDFLjava/lang/Object;BSC)I";
  jmethodID mix = FN(env, 33, jmethodID (*)(Env, jobject, const char *, const char *))(env, thing, "mix", mixed);
  jmethodID mixStatic = FN(env, 113, jmethodID (*)(Env, jobject, const char *, const char *))(env, thing, "mixStatic", mixed);
  jvalue values[8];
  values[0].i = -7; values[1].j = 0x123456789abcdef0LL; values[2].d = 2.5; values[3].f = 1.25f;
  values[4].l = self; values[5].b = -3; values[6].s = -300; values[7].c = 0xBEEF;
#define MIXED -7, 0x123456789abcdef0LL, 2.5, 1.25f, self, (jbyte)-3, (jshort)-300, (jchar)0xBEEF
  if (FN(env, 49, jint (*)(Env, jobject, jmethodID, ...))(env, self, mix, MIXED) == 0xFF) found |= 1 << 9;
  if (byList(env, 50, self, 0, mix, MIXED) == 0xFF) found |= 1 << 10;
  if (FN(env, 51, jint (*)(Env, jobject, jmethodID, const jvalue *))(env, self, mix, values) == 0xFF) found |= 1 << 11;
  if (FN(env, 129, jint (*)(Env, jobject, jmethodID, ...))(env, thing, mixStatic, MIXED) == 0xFF) found |= 1 << 12;
  if (byList(env, 130, thing, 0, mixStatic, MIXED) == 0xFF) found |= 1 << 13;
  if (FN(env, 131, jint (*)(Env, jobject, jmethodID, const jvalue *))(env, thing, mixStatic, values) == 0xFF) found |= 1 << 14;
  if (FN(env, 79, jint (*)(Env, jobject, jobject, jmethodID, ...))(env, self, thing, mix, MIXED) == 0xFF) found |= 1 << 15;
  if (byList(env, 80, self, thing, mix, MIXED) == 0xFF) found |= 1 << 16;
  if (FN(env, 81, jint (*)(Env, jobject, jobject, jmethodID, const jvalue *))(env, self, thing, mix, values) == 0xFF)
    found |= 1 << 17;
  return found;
}

int main(void) { return 0; }
