// Tiny stack VM for make.fun's ISA v1 (kit: program/generator/subject/ISA.md).
// For each id under $MAKEFUN_INPUT_DIR (default /input) it runs program.bin
// against input.bin and writes stdout.bin + exit.txt under
// $MAKEFUN_OUTPUT_DIR (default /output). Signed 32-bit wrapping values;
// every trap keeps the output written before it.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// opcode -> [immediate bytes, pops, pushes]; absence means unknown opcode.
const OPS: Record<number, [number, number, number]> = {
  0x00: [0, 0, 0], 0x01: [1, 0, 1], 0x02: [4, 0, 1], 0x03: [0, 1, 0],
  0x04: [0, 1, 2], 0x05: [0, 2, 2], 0x06: [0, 2, 3], 0x07: [0, 3, 3],
  0x10: [0, 2, 1], 0x11: [0, 2, 1], 0x12: [0, 2, 1], 0x13: [0, 2, 1],
  0x14: [0, 2, 1], 0x15: [0, 2, 1], 0x16: [0, 2, 1], 0x17: [0, 1, 1],
  0x18: [0, 2, 1], 0x19: [0, 2, 1], 0x1a: [0, 2, 1], 0x1b: [0, 1, 1],
  0x1c: [0, 2, 1], 0x1d: [0, 2, 1], 0x1e: [0, 2, 1], 0x20: [0, 2, 1],
  0x21: [0, 2, 1], 0x22: [0, 2, 1], 0x30: [2, 0, 0], 0x31: [2, 1, 0],
  0x32: [2, 1, 0], 0x33: [2, 0, 0], 0x34: [0, 0, 0], 0x40: [0, 1, 1],
  0x41: [0, 2, 0], 0x50: [0, 1, 0], 0x51: [0, 1, 0], 0x52: [0, 0, 1],
  0x53: [0, 1, 0],
};

function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const stack = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: out.slice(0, olen), code });

  for (;;) {
    if (steps === 1_000_000) return end(10); // step limit
    if (pc < 0 || pc >= n) return end(9); // pc outside program
    const spec = OPS[prog[pc]];
    if (!spec) return end(5); // unknown opcode
    const [imm, pops, pushes] = spec;
    if (pc + imm >= n) return end(9); // immediate cut off by program end
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return end(2); // stack underflow
    if (sp - pops + pushes > 256) return end(3); // stack overflow
    const op = prog[pc];
    pc = next;
    switch (op) {
      case 0x00: return end(0); // HALT
      case 0x01: stack[sp++] = (prog[next - 1] << 24) >> 24; break; // PUSH8 sign-extended
      case 0x02: // PUSH32 little-endian
        stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03: sp--; break; // POP
      case 0x04: stack[sp] = stack[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; break; } // SWAP
      case 0x06: stack[sp] = stack[sp - 2]; sp++; break; // OVER
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = stack[sp - 3]; stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a;
        break;
      }
      case 0x17: stack[sp - 1] = -stack[sp - 1] | 0; break; // NEG wraps
      case 0x1b: stack[sp - 1] = ~stack[sp - 1]; break; // NOT
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1], a = stack[sp - 2];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // low 32 bits of exact product
        else if (op === 0x13) { if (b === 0) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { if (b === 0) return end(4); r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        sp -= 2; stack[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed rel16 from next pc
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (!take) { const v = stack[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit absolute target
        if (csp === 64) return end(7);
        calls[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34: // RET
        if (csp === 0) return end(8);
        pc = calls[--csp];
        break;
      case 0x40: { // LOAD
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE ( v addr -- )
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return end(6);
        mem[addr] = stack[sp - 2]; sp -= 2;
        break;
      }
      case 0x50: { // PRINT decimal ASCII; writes nothing if past the output cap
        const s = String(stack[sp - 1]);
        if (olen + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (olen + 1 > 65536) return end(11);
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52: stack[sp++] = ip < input.length ? input[ip++] : -1; break; // IN, -1 past end forever
      case 0x53: return end(stack[--sp] & 255); // EXIT low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const prog = new Uint8Array(readFileSync(join(I, id, 'program.bin')));
  const input = new Uint8Array(readFileSync(join(I, id, 'input.bin')));
  const r = run(prog, input);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
