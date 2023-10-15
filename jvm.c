#include "jvm.h"

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "heap.h"
#include "read_class.h"

/** The name of the method to invoke to run the class file */
const char MAIN_METHOD[] = "main";
/**
 * The "descriptor" string for main(). The descriptor encodes main()'s signature,
 * i.e. main() takes a String[] and returns void.
 * If you're interested, the descriptor string is explained at
 * https://docs.oracle.com/javase/specs/jvms/se12/html/jvms-4.html#jvms-4.3.2.
 */
const char MAIN_DESCRIPTOR[] = "([Ljava/lang/String;)V";

/**
 * Represents the return value of a Java method: either void or an int or a reference.
 * For simplification, we represent a reference as an index into a heap-allocated array.
 * (In a real JVM, methods could also return object references or other primitives.)
 */
typedef struct {
    /** Whether this returned value is an int */
    bool has_value;
    /** The returned value (only valid if `has_value` is true) */
    int32_t value;
} optional_value_t;

/**
 * Runs a method's instructions until the method returns.
 *
 * @param method the method to run
 * @param locals the array of local variables, including the method parameters.
 *   Except for parameters, the locals are uninitialized.
 * @param class the class file the method belongs to
 * @param heap an array of heap-allocated pointers, useful for references
 * @return an optional int containing the method's return value
 */
optional_value_t execute(method_t *method, int32_t *locals, class_file_t *class,
                         heap_t *heap) {
    optional_value_t result = {.has_value = false};
    int *stack = malloc(sizeof(int) * (1 + method->code.max_stack));
    if (!stack) {
        fprintf(stderr, "Memory allocation failure for stack\n");
        exit(EXIT_FAILURE);
    }
    stack[0] = 0;
    u2 idx = 0;
    int cont = 1;

    for (u4 curr = 0; curr < method->code.code_length; curr++) {
        if (cont == 0) {
            break;
        }
        u1 mnemonic = method->code.code[curr];
        if (mnemonic != i_invokestatic) {
            switch (mnemonic) {
                case i_bipush:
                    curr++;

                    stack[idx] = (int32_t) (int8_t) method->code.code[curr];
                    idx++;
                    break;
                case i_iadd:
                    if (idx >= 2) {
                        stack[idx - 2] = stack[idx - 2] + stack[idx - 1];
                        idx--;
                    }
                    else {
                        fprintf(stderr, "Index out of bounds\n");
                    }
                    break;

                case i_isub:
                    stack[idx - 2] = stack[idx - 2] - stack[idx - 1];
                    idx--;
                    break;
                case i_imul:
                    stack[idx - 2] = stack[idx - 2] * stack[idx - 1];
                    idx--;
                    break;
                case i_idiv:
                    stack[idx - 2] = stack[idx - 2] / stack[idx - 1];
                    idx--;
                    break;
                case i_irem:
                    stack[idx - 2] = stack[idx - 2] % stack[idx - 1];
                    idx--;
                    break;
                case i_ineg:
                    stack[idx - 1] = (i_iconst_m1 - i_iconst_0) * stack[idx - 1];
                    break;
                case i_ishl:
                    stack[idx - 2] = stack[idx - 2] << stack[idx - 1];
                    idx--;
                    break;
                case i_ishr:
                    stack[idx - 2] = stack[idx - 2] >> stack[idx - 1];
                    idx--;
                    break;
                case i_iushr:
                    stack[idx - 2] = ((u4) stack[idx - 2]) >> stack[idx - 1];
                    idx--;
                    break;
                case i_iand:
                    stack[idx - 2] = stack[idx - 2] & stack[idx - 1];
                    idx--;
                    break;
                case i_ior:
                    stack[idx - 2] = stack[idx - 2] | stack[idx - 1];
                    idx--;
                    break;
                case i_ixor:
                    stack[idx - 2] = stack[idx - 2] ^ stack[idx - 1];
                    idx--;
                    break;
                case i_getstatic:
                    curr += 2;
                    break;
                case i_return:
                    curr++;
                    cont = 0;
                    break;
                case i_invokevirtual:
                    idx--;
                    printf("%d\n", stack[idx]);
                    curr += 2;
                    break;
                case i_iconst_m1 ... i_iconst_5:
                    stack[idx] = mnemonic - i_iconst_0;
                    idx++;
                    break;
                case i_sipush:
                    stack[idx] =
                        (int16_t) (((int16_t) method->code.code[curr + 1] << 0x08) |
                                   (int16_t) method->code.code[curr + 2]);
                    idx++;
                    curr += 2;
                    break;
                case i_aload:
                case i_iload:
                    assert(idx < method->code.max_stack);
                    assert(curr + 1 < method->code.code_length);
                    unsigned char ubyte1 = method->code.code[curr + 1];
                    stack[idx] = locals[ubyte1];
                    curr++;
                    idx++;
                    break;
                case i_astore:
                case i_istore:
                    curr++;
                    locals[method->code.code[curr]] = stack[idx - 1];
                    idx--;
                    break;
                case i_iload_0 ... i_iload_3:
                    stack[idx] = locals[mnemonic - i_iload_0];
                    idx++;
                    break;
                case i_istore_0 ... i_istore_3:
                    locals[mnemonic - i_istore_0] = stack[idx - 1];
                    idx--;
                    break;
                case i_iinc:
                    locals[(u1) method->code.code[curr + 1]] +=
                        (int8_t) method->code.code[curr + 2];
                    curr += 2;
                    break;

                case i_ldc:
                    curr++;
                    cp_info cp = class->constant_pool[(u1) method->code.code[curr] - 1];
                    if (cp.tag == CONSTANT_Integer) {
                        if (idx < 0 || idx >= method->code.max_stack) {
                            fprintf(stderr, "Stack index out of bounds!\n");
                            exit(1);
                        }
                        stack[idx] = ((CONSTANT_Integer_info *) cp.info)->bytes;
                        idx++;
                    }
                    break;
                case i_if_icmpeq ... i_if_icmple:
                    if ((mnemonic == i_if_icmpeq && stack[idx - 2] == stack[idx - 1]) ||
                        (mnemonic == i_if_icmpne && stack[idx - 2] != stack[idx - 1]) ||
                        (mnemonic == i_if_icmplt && stack[idx - 2] < stack[idx - 1]) ||
                        (mnemonic == i_if_icmpge && stack[idx - 2] >= stack[idx - 1]) ||
                        (mnemonic == i_if_icmpgt && stack[idx - 2] > stack[idx - 1]) ||
                        (mnemonic == i_if_icmple && stack[idx - 2] <= stack[idx - 1])) {
                        curr += ((int16_t) ((method->code.code[curr + 1] << 8) |
                                            method->code.code[curr + 2])) -
                                1;
                    }
                    else {
                        curr += 2;
                    }
                    idx -= 2;
                    break;
                case i_goto:
                    curr += ((int16_t) ((method->code.code[curr + 1] << 8) |
                                        method->code.code[curr + 2])) -
                            1;
                    break;
                case i_ireturn:
                    idx--;
                    result = (optional_value_t){.has_value = true, .value = stack[idx]};
                    curr++;
                    cont = 0;
                    break;
                case i_ifeq ... i_ifle:
                    idx--;
                    if ((mnemonic == i_ifeq && stack[idx] == 0) ||
                        (mnemonic == i_ifne && stack[idx] != 0) ||
                        (mnemonic == i_iflt && stack[idx] < 0) ||
                        (mnemonic == i_ifge && stack[idx] >= 0) ||
                        (mnemonic == i_ifgt && stack[idx] > 0) ||
                        (mnemonic == i_ifle && stack[idx] <= 0)) {
                        curr += ((int16_t) ((method->code.code[curr + 1] << 8) |
                                            method->code.code[curr + 2])) -
                                1;
                    }
                    else {
                        curr += 2;
                    }
                    break;

                case i_nop:
                case i_dup:
                    stack[idx] = stack[idx - 1];
                    idx++;
                    break;

                case i_newarray: {
                    curr++;
                    int32_t count = stack[--idx];
                    int32_t *rawArray = calloc(count + 1, sizeof(int32_t));
                    rawArray[0] = count;

                    int32_t ref = heap_add(heap, rawArray);
                    stack[idx++] = ref;
                    break;
                }

                case i_arraylength: {
                    int32_t ref = stack[--idx];
                    int32_t *array = heap_get(heap, ref);
                    stack[idx++] = array[0];
                    break;
                }

                case i_areturn:
                    result = (optional_value_t){.has_value = true, .value = stack[--idx]};
                    curr = method->code.code_length;
                    break;

                case i_iastore: {
                    int32_t value = stack[--idx];
                    int32_t index = stack[--idx];
                    int32_t ref = stack[--idx];
                    int32_t *array = heap_get(heap, ref);
                    if (index < 0 || index >= array[0]) {
                        fprintf(stderr,
                                "Array index out of bounds during i_iastore: %d\n",
                                index);
                        exit(1);
                    }
                    array[index + 1] = value;
                    break;
                }

                case i_iaload: {
                    int32_t index = stack[--idx];
                    int32_t ref = stack[--idx];
                    int32_t *array = heap_get(heap, ref);
                    if (index < 0 || index >= array[0]) {
                        fprintf(stderr, "Array index out of bounds during i_iaload: %d\n",
                                index);
                        exit(1);
                    }
                    stack[idx++] = array[index + 1];
                    break;
                }

                case i_aload_0 ... i_aload_3:
                    stack[idx] = locals[(u1) mnemonic - i_aload_0];
                    idx++;
                    break;
                case i_astore_0 ... i_astore_3:
                    locals[mnemonic - i_astore_0] = stack[idx - 1];
                    idx--;
                    break;

                default:
                    fprintf(stderr, "Unsupported opcode: %x\n", mnemonic);
                    exit(EXIT_FAILURE);
            }
        }
        else {
            method_t *m = find_method_from_index(
                (u2) ((method->code.code[curr + 1] << 8) | method->code.code[curr + 2]),
                class);
            uint16_t num_params = get_number_of_parameters(m);
            int32_t l[m->code.max_locals];
            memset(l, 0, m->code.max_locals);
            for (u2 i = 0; i < num_params; i++) {
                l[i] = stack[idx - num_params + i];
            }
            idx -= num_params;
            if (idx < 0) {
                fprintf(stderr, "index out of bounds");
                exit(1);
            }
            optional_value_t res = execute(m, l, class, heap);
            if (res.has_value) {
                stack[idx] = res.value;
                idx++;
            }
            curr += 2;
        }
    }
    free(stack);
    return result;
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "USAGE: %s <class file>\n", argv[0]);
        return 1;
    }

    // Open the class file for reading
    FILE *class_file = fopen(argv[1], "r");
    assert(class_file != NULL && "Failed to open file");

    // Parse the class file
    class_file_t *class = get_class(class_file);
    int error = fclose(class_file);
    assert(error == 0 && "Failed to close file");

    // The heap array is initially allocated to hold zero elements.
    heap_t *heap = heap_init();

    // Execute the main method
    method_t *main_method = find_method(MAIN_METHOD, MAIN_DESCRIPTOR, class);
    assert(main_method != NULL && "Missing main() method");
    /* In a real JVM, locals[0] would contain a reference to String[] args.
     * But since TeenyJVM doesn't support Objects, we leave it uninitialized. */
    int32_t locals[main_method->code.max_locals];
    // Initialize all local variables to 0
    memset(locals, 0, sizeof(locals));
    optional_value_t result = execute(main_method, locals, class, heap);
    assert(!result.has_value && "main() should return void");

    // Free the internal data structures
    free_class(class);

    // Free the heap
    heap_free(heap);
}
