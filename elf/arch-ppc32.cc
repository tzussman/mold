#include "mold.h"

namespace mold::elf {

using E = PPC32;

static u64 lo(u64 x)       { return x & 0xffff; }
static u64 hi(u64 x)       { return x >> 16; }
static u64 ha(u64 x)       { return (x + 0x8000) >> 16; }
static u64 high(u64 x)     { return (x >> 16) & 0xffff; }
static u64 higha(u64 x)    { return ((x + 0x8000) >> 16) & 0xffff; }
static u64 higher(u64 x)   { return (x >> 32) & 0xffff; }
static u64 highera(u64 x)  { return ((x + 0x8000) >> 32) & 0xffff; }
static u64 highest(u64 x)  { return x >> 48; }
static u64 highesta(u64 x) { return (x + 0x8000) >> 48; }

template <>
void write_plt_header(Context<E> &ctx, u8 *buf) {
  static const ub32 insn[] = {
    0x7c08'02a6, // mflr    r0
    0x429f'0005, // bcl     20, 31, 4 // obtain PC
    0x7d88'02a6, // mflr    r12
    0x7c08'03a6, // mtlr    r0

    0x3d6b'0000, // addis   r11, r11, _GLOBAL_OFFSET_TABLE_@ha
    0x396b'001c, // addi    r11, r11, _GLOBAL_OFFSET_TABLE_@lo
    0x7d6c'5850, // subf    r11, r12, r11
    0x3d8c'0002, // addis   r12, r12, 2
    0x800c'f7f0, // lwz     r0,  -2064(r12)
    0x818c'f7f4, // lwz     r12, -2060(r12)
    0x7c09'03a6, // mtctr   r0
    // Triple r11
    0x7c0b'5a14, // add     r0,  r11, r11
    0x7d60'5a14, // add     r11, r0,  r11
    0x4e80'0420, // bctr
  };

  static_assert(sizeof(insn) == E::plt_hdr_size);
  memcpy(buf, insn, sizeof(insn));
  *(ub64 *)(buf + 44) = ctx.gotplt->shdr.sh_addr - ctx.plt->shdr.sh_addr - 8;
}

template <>
void write_plt_entry(Context<E> &ctx, u8 *buf, Symbol<E> &sym) {
  // b plt0
  *(ub32 *)buf = 0x4800'0000;
  *(ub32 *)buf |= (ctx.plt->shdr.sh_addr - sym.get_plt_addr(ctx)) & 0x00ff'ffff;
}

template <>
void write_pltgot_entry(Context<E> &ctx, u8 *buf, Symbol<E> &sym) {
  *(ub32 *)buf = 0x6000'0000; // nop
}

template <>
void EhFrameSection<E>::apply_reloc(Context<E> &ctx, const ElfRel<E> &rel,
                                    u64 offset, u64 val) {
  u8 *loc = ctx.buf + this->shdr.sh_offset + offset;

  switch (rel.r_type) {
  case R_PPC_REL32:
    *(ub32 *)loc = val - this->shdr.sh_addr - offset;
    break;
  default:
    Fatal(ctx) << "unsupported relocation in .eh_frame: " << rel;
  }
}

template <>
void InputSection<E>::apply_reloc_alloc(Context<E> &ctx, u8 *base) {
  std::span<const ElfRel<E>> rels = get_rels(ctx);

  ElfRel<E> *dynrel = nullptr;
  if (ctx.reldyn)
    dynrel = (ElfRel<E> *)(ctx.buf + ctx.reldyn->shdr.sh_offset +
                           file.reldyn_offset + this->reldyn_offset);

  for (i64 i = 0; i < rels.size(); i++) {
    const ElfRel<E> &rel = rels[i];
    if (rel.r_type == R_NONE)
      continue;

    Symbol<E> &sym = *file.symbols[rel.r_sym];
    u8 *loc = base + rel.r_offset;

    auto check = [&](i64 val, i64 lo, i64 hi) {
      if (val < lo || hi <= val)
        Error(ctx) << *this << ": relocation " << rel << " against "
                   << sym << " out of range: " << val << " is not in ["
                   << lo << ", " << hi << ")";
    };

#define S   sym.get_addr(ctx)
#define A   rel.r_addend
#define P   (get_addr() + rel.r_offset)
#define G   (sym.get_got_idx(ctx) * sizeof(Word<E>))
#define GOT ctx.got->shdr.sh_addr

    switch (rel.r_type) {
    case R_PPC_ADDR32:
    case R_PPC_UADDR32:
      apply_dyn_absrel(ctx, sym, rel, loc, S, A, P, dynrel);
      break;
    case R_PPC_ADDR14:
      *(ub32 *)loc &= 0b1100'0000'0000'0000'1111'1111'1111'1111;
      *(ub32 *)loc |= bits(S + A, 15, 2) << 16;
      break;
    case R_PPC_ADDR16:
    case R_PPC_UADDR16:
    case R_PPC_ADDR16_LO:
    case R_PPC_PLT16_LO:
      *(ub16 *)loc |= S + A;
      break;
    case R_PPC_ADDR16_HI:
    case R_PPC_PLT16_HI:
      *(ub16 *)loc |= hi(S + A);
      break;
    case R_PPC_ADDR16_HA:
    case R_PPC_PLT16_HA:
      *(ub16 *)loc |= ha(S + A);
      break;
    case R_PPC_ADDR24:
      *(ub32 *)loc &= 0b1100'0000'0000'0000'0000'0000'0011'1111;
      *(ub32 *)loc |= bits(S + A, 25, 2) << 6;
      break;
    case R_PPC_ADDR30:
      *(ub32 *)loc &= 0b1100'0000'0000'0000'0000'0000'0000'0000;
      *(ub32 *)loc |= bits(S + A, 31, 2);
      break;
    case R_PPC_PLT32:
      *(ub32 *)loc |= S + A;
      break;
    case R_PPC_REL14:
      *(ub32 *)loc &= 0b1100'0000'0000'0000'1111'1111'1111'1111;
      *(ub32 *)loc |= bits(S + A - P, 15, 2) << 16;
      break;
    case R_PPC_REL16:
    case R_PPC_REL16_LO:
      *(ub16 *)loc = S + A - P;
      break;
    case R_PPC_REL16_HI:
      *(ub16 *)loc = hi(S + A - P);
      break;
    case R_PPC_REL16_HA:
      *(ub16 *)loc = ha(S + A - P);
      break;
    case R_PPC_REL24:
      *(ub32 *)loc &= 0b1100'0000'0000'0000'0000'0000'0011'1111;
      *(ub32 *)loc |= bits(S + A - P, 25, 2) << 6;
      break;
    case R_PPC_PLTREL24: {
      i64 val = S - P;

      if (sym.has_plt(ctx) || sign_extend(val, 25) != val) {
        RangeExtensionRef ref = extra.range_extn[i];
        assert(ref.thunk_idx != -1);
        val = output_section->thunks[ref.thunk_idx]->get_addr(ref.sym_idx) - P;
      }

      *(ub32 *)loc &= 0b1100'0000'0000'0000'0000'0000'0011'1111;
      *(ub32 *)loc |= bits(val, 25, 2) << 6;
      break;
    }
    case R_PPC_REL32:
    case R_PPC_PLTREL32:
      *(ub32 *)loc |= S + A - P;
      break;
    case R_PPC_LOCAL24PC:
      // TODO: implement
      break;
    case R_PPC_GOT16:
    case R_PPC_GOT16_LO:
      *(ub16 *)loc = G + A;
      break;
    case R_PPC_GOT16_HI:
      *(ub16 *)loc = hi(G + A);
      break;
    case R_PPC_GOT16_HA:
      *(ub16 *)loc = ha(G + A);
      break;
    default:
      Fatal(ctx) << *this << ": apply_reloc_alloc relocation: " << rel;
    }

#undef S
#undef A
#undef P
#undef G
#undef GOT
  }
}

template <>
void InputSection<E>::apply_reloc_nonalloc(Context<E> &ctx, u8 *base) {
  std::span<const ElfRel<E>> rels = get_rels(ctx);

  for (i64 i = 0; i < rels.size(); i++) {
    const ElfRel<E> &rel = rels[i];
    if (rel.r_type == R_NONE)
      continue;

    Symbol<E> &sym = *file.symbols[rel.r_sym];
    u8 *loc = base + rel.r_offset;

    if (!sym.file) {
      record_undef_error(ctx, rel);
      continue;
    }

    auto check = [&](i64 val, i64 lo, i64 hi) {
      if (val < lo || hi <= val)
        Error(ctx) << *this << ": relocation " << rel << " against "
                   << sym << " out of range: " << val << " is not in ["
                   << lo << ", " << hi << ")";
    };

    SectionFragment<E> *frag;
    i64 frag_addend;
    std::tie(frag, frag_addend) = get_fragment(ctx, rel);

#define S (frag ? frag->get_addr(ctx) : sym.get_addr(ctx))
#define A (frag ? frag_addend : (i64)rel.r_addend)

    switch (rel.r_type) {
    default:
      Fatal(ctx) << *this << ": apply_reloc_nonalloc: " << rel;
    }

#undef S
#undef A
  }
}

template <>
void InputSection<E>::scan_relocations(Context<E> &ctx) {
  assert(shdr().sh_flags & SHF_ALLOC);

  this->reldyn_offset = file.num_dynrel * sizeof(ElfRel<E>);
  std::span<const ElfRel<E>> rels = get_rels(ctx);

  // Scan relocations
  for (i64 i = 0; i < rels.size(); i++) {
    const ElfRel<E> &rel = rels[i];
    if (rel.r_type == R_NONE)
      continue;

    Symbol<E> &sym = *file.symbols[rel.r_sym];

    if (!sym.file) {
      record_undef_error(ctx, rel);
      continue;
    }

    if (sym.is_ifunc())
      sym.flags |= (NEEDS_GOT | NEEDS_PLT);

    switch (rel.r_type) {
    case R_PPC_ADDR32:
    case R_PPC_UADDR32:
      scan_rel(ctx, sym, rel, dyn_absrel_table);
      break;
    case R_PPC_ADDR14:
    case R_PPC_ADDR16:
    case R_PPC_UADDR16:
    case R_PPC_ADDR16_LO:
    case R_PPC_ADDR16_HI:
    case R_PPC_ADDR16_HA:
    case R_PPC_ADDR24:
    case R_PPC_ADDR30:
      scan_rel(ctx, sym, rel, absrel_table);
      break;
    case R_PPC_REL14:
    case R_PPC_REL16:
    case R_PPC_REL16_LO:
    case R_PPC_REL16_HI:
    case R_PPC_REL16_HA:
    case R_PPC_REL24:
    case R_PPC_REL32:
    case R_PPC_LOCAL24PC:
      scan_rel(ctx, sym, rel, pcrel_table);
      break;
    case R_PPC_GOT16:
    case R_PPC_GOT16_LO:
    case R_PPC_GOT16_HI:
    case R_PPC_GOT16_HA:
      sym.flags |= NEEDS_GOT;
      break;
    case R_PPC_PLT16_LO:
    case R_PPC_PLT16_HI:
    case R_PPC_PLT16_HA:
    case R_PPC_PLT32:
    case R_PPC_PLTREL24:
    case R_PPC_PLTREL32:
      if (sym.is_imported)
        sym.flags |= NEEDS_PLT;
      break;
    default:
      Fatal(ctx) << *this << ": scan_relocations: " << rel;
    }
  }
}

template <>
void RangeExtensionThunk<E>::copy_buf(Context<E> &ctx) {
  u8 *buf = ctx.buf + output_section.shdr.sh_offset + offset;

  static const ub32 plt_thunk[] = {
    // Get the address of this thunk
    0x7c08'02a6, // mflr    %r0
    0x429f'0005, // bcl     20, 31, 4
    0x7d68'02a6, // mflr    %r11
    0x7c08'03a6, // mtlr    %r0

    // Load an address from .got/.got.plt and jump there
    0x3d6b'0000, // addis   %r11, (GOTPLT_ENTRY - THUNK_ADDR)@ha
    0x816b'0000, // lwz     %r11, (GOTPLT_ENTRY - THUNK_ADDR)@l(%r11)
    0x7d69'03a6, // mtctr   %r11
    0x4e80'0420, // bctr
  };

  static_assert(E::thunk_size == sizeof(plt_thunk));

  for (i64 i = 0; i < symbols.size(); i++) {
    Symbol<E> &sym = *symbols[i];

    u64 got = sym.has_got(ctx) ? sym.get_got_addr(ctx) : sym.get_gotplt_addr(ctx);
    u64 thunk = get_addr(i);

    ub32 *loc = (ub32 *)(buf + i * E::thunk_size);
    memcpy(loc, plt_thunk, sizeof(plt_thunk));
    loc[4] |= higha(got - thunk);
    loc[5] |= lo(got - thunk);
  }
}

} // namespace mold::elf
