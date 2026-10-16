#include <stdlib.h>
#include <string.h>

#include <caml/memory.h>
#include <caml/fail.h>
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/bigarray.h>
#include <caml/compatibility.h>
#include <caml/callback.h>

#include "llvm_loader.h"
#include "llvm_loader_stubs.h"

static void failn(int n) {
    caml_raise_with_arg(*caml_named_value("Llvm_loader_fail"), Val_int(n));
}

static void loader_fail(const struct bap_llvm_loader *loader, int n) {
    bap_llvm_loader_destroy(loader);
    failn(n);
}

value bap_llvm_load_stub(value arg, value pdb_path) {
    CAMLparam2(arg, pdb_path);
    CAMLlocal1(result);
    const struct caml_ba_array* array = Caml_ba_array_val(arg);
    if ((!array->dim[0]) || (array->num_dims != 1))
        failn(1);
    char * pdb = strdup(String_val(pdb_path));
    const struct bap_llvm_loader *loader =
        bap_llvm_loader_create((const char*)(array->data), array->dim[0], pdb);
    free(pdb);
    if (bap_llvm_file_not_supported(loader))
        loader_fail(loader, 2);
    if (bap_llvm_loader_failed(loader))
        loader_fail(loader, 1);
    /* the document is binary, see llvm_loader_utils.hpp */
    size_t size = bap_llvm_loader_size(loader);
    void *data = malloc(size);
    if (!data) {
        bap_llvm_loader_destroy(loader);
        caml_raise_out_of_memory();
    }
    memcpy(data, bap_llvm_loader_data(loader), size);
    bap_llvm_loader_destroy(loader);
    result = caml_ba_alloc_dims(CAML_BA_CHAR | CAML_BA_C_LAYOUT | CAML_BA_MANAGED,
                                1, data, (intnat) size);
    CAMLreturn(result);
}
