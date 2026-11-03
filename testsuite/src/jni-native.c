// What native code does with JNI, called by the host with an environment that a model serves: classes, methods with their
// arguments and results of each width, strings, objects, and the VM and its environment. Each bit of what `run` gives is one thing
// that came out as it should. The table is the one of jni.h, by index.
#include <stdint.h>

typedef int32_t jint;
typedef int64_t jlong;
typedef void *jobject;
typedef void *jmethodID;
typedef void *Env;

#define TABLE(env) (*(void ***)(env))
#define FN(env, index, type) ((type)(TABLE(env)[index]))

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
  return found;
}

int main(void) { return 0; }
