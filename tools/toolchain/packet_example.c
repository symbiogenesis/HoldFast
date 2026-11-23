/* SPDX-License-Identifier: Apache-2.0 */
#include <stdio.h>

/* Use the generated validator and its span representation with an interactive driver. */
#define main holdfast_qualification_main
#include "packet.c"
#undef main

static void show_bytes(const char *label, const unsigned char *bytes, unsigned long length)
{
    printf("%s", label);
    for (unsigned long i = 0; i < length; ++i) {
        printf(" %02X", (unsigned int)bytes[i]);
    }
    putchar('\n');
}

int main(void)
{
    unsigned char backing[32];
    struct holdfast_span_byte dst, pkt;
    struct holdfast_Result_ValidatedPacket_ValidationError result;
    holdfast_span_alloc_zeroed(&dst, backing, 0, 9);
    holdfast_span_fill(&dst, &dst, 0, 8, 0xCC);
    holdfast_span_write(&dst, &dst, 8, 0xA5);
    holdfast_span_alloc_zeroed(&pkt, backing, 16, 8);
    pkt.length = fread(pkt.ptr, 1, pkt.length, stdin);
    if (ferror(stdin)) {
        perror("packet input");
        return 1;
    }

    show_bytes("packet", pkt.ptr, pkt.length);
    show_bytes("before", dst.ptr, dst.length);
    PrepareAndValidatePacket(&result, &dst, &pkt);
    if (result.is_ok) {
        struct holdfast_span_byte view = result.ok.PayloadView;
        if (!view.tag || !view.perm_read || view.base < dst.base
            || view.base - dst.base > dst.length || view.length > dst.length - (view.base - dst.base)
            || view.ptr != dst.ptr + (view.base - dst.base)) {
            fputs("invalid returned destination view\n", stderr);
            return 1;
        }
        printf("Ok copied=%lu offset=%lu length=%lu read=%d write=%d\n",
               result.ok.CopiedBytes, view.base - dst.base, view.length, view.perm_read, view.perm_write);
        show_bytes("payload", view.ptr, view.length);
    } else {
        const char *name;
        switch (result.err) {
        case VOS_ERR_FramingShort: name = "FramingShort"; break;
        case VOS_ERR_BadMagicOrFlags: name = "BadMagicOrFlags"; break;
        case VOS_ERR_LengthOutOfBounds: name = "LengthOutOfBounds"; break;
        case VOS_ERR_ChecksumRejected: name = "ChecksumRejected"; break;
        default: fputs("unknown validation error\n", stderr); return 1;
        }
        printf("Err(%s)\n", name);
    }
    show_bytes("after ", dst.ptr, dst.length);
    return 0;
}
