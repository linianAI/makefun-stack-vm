// tiny-stack-vm: an exact interpreter for make.fun's tiny stack ISA (rules in the
// kit's ISA.md), traps and limits included. It answers every instance in the input
// directory: program.bin run against input.bin, stdout.bin and exit.txt written.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode [immediate bytes, popped, pushed] by opcode byte; null names no opcode.
const META = [];
for (let i = 0; i < 256; i++) META.push(null);
function def(op, imm, pops, pushes) {
  META[op] = [imm, pops, pushes];
}
def(0x00, 0, 0, 0); def(0x01, 1, 0, 1); def(0x02, 4, 0, 1); // HALT, PUSH8, PUSH32
def(0x03, 0, 1, 0); def(0x04, 0, 1, 2); def(0x05, 0, 2, 2); // POP, DUP, SWAP
def(0x06, 0, 2, 3); def(0x07, 0, 3, 3); // OVER, ROT
def(0x17, 0, 1, 1); def(0x1b, 0, 1, 1); // NEG, NOT
def(0x30, 2, 0, 0); def(0x31, 2, 1, 0); def(0x32, 2, 1, 0); // JMP, JZ, JNZ
def(0x33, 2, 0, 0); def(0x34, 0, 0, 0); // CALL, RET
def(0x40, 0, 1, 1); def(0x41, 0, 2, 0); // LOAD, STORE
def(0x50, 0, 1, 0); def(0x51, 0, 1, 0); def(0x52, 0, 0, 1); def(0x53, 0, 1, 0); // PRINT, PUTC, IN, EXIT
for (const op of [0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22]) {
  def(op, 0, 2, 1); // the two-operand arithmetic, bitwise, shift and comparison block
}

// Runs one program to its end; a trap ends it at once with the trap's code, keeps
// the output written before it, and the trapping instruction writes nothing.
function run(prog, input) {
  const n = prog.length;
  const stack = new Int32Array(256);
  let sp = 0;
  const calls = new Int32Array(64);
  let csp = 0;
  const mem = new Int32Array(256);
  const out = [];
  let inPos = 0;
  let pc = 0;
  let steps = 0;
  const finish = (code) => ({ bytes: Uint8Array.from(out), code });
  for (;;) {
    // One step, in the ISA's order: step limit, pc range, opcode, immediate, stack.
    if (steps === 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const meta = META[prog[pc]];
    if (meta === null) return finish(5);
    const imm = meta[0];
    if (pc + imm >= n) return finish(9);
    steps++;
    if (sp < meta[1]) return finish(2);
    if (sp - meta[1] + meta[2] > 256) return finish(3);
    const op = prog[pc];
    const next = pc + 1 + imm;
    pc = next;
    switch (op) {
      case 0x00:
        return finish(0);
      case 0x01: // PUSH8, sign-extended
        stack[sp++] = (prog[next - 1] << 24) >> 24;
        break;
      case 0x02: // PUSH32, little-endian signed
        stack[sp++] = prog[next - 4] | (prog[next - 3] << 8) | (prog[next - 2] << 16) | (prog[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04: // DUP
        stack[sp] = stack[sp - 1];
        sp++;
        break;
      case 0x05: { // SWAP
        const t = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = t;
        break;
      }
      case 0x06: // OVER
        stack[sp] = stack[sp - 2];
        sp++;
        break;
      case 0x07: { // ROT: ( a b c -- b c a )
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = a;
        break;
      }
      case 0x17: // NEG, wrapping
        stack[sp - 1] = -stack[sp - 1] | 0;
        break;
      case 0x1b:
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1];
        const a = stack[sp - 2];
        let r;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // MUL: exact low 32 bits
        else if (op === 0x13) { if (b === 0) return finish(4); r = (a / b) | 0; } // DIV: toward zero
        else if (op === 0x14) { if (b === 0) return finish(4); r = (a % b) | 0; } // MOD: sign of a
        else if (op === 0x15) { if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
        else if (op === 0x16) { if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31); // shift counts use the low 5 bits
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU: unsigned
        stack[sp - 2] = r;
        sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: { // JMP, JZ, JNZ: target = next + signed offset
        const rel = ((prog[next - 2] | (prog[next - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (!take) {
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33: // CALL: unsigned absolute target
        if (csp === 64) return finish(7);
        calls[csp++] = next;
        pc = prog[next - 2] | (prog[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return finish(8);
        pc = calls[--csp];
        break;
      case 0x40: { // LOAD
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return finish(6);
        stack[sp - 1] = mem[addr];
        break;
      }
      case 0x41: { // STORE: ( v addr -- )
        const addr = stack[sp - 1];
        if (addr < 0 || addr > 255) return finish(6);
        mem[addr] = stack[sp - 2];
        sp -= 2;
        break;
      }
      case 0x50: { // PRINT: past the output limit writes nothing, traps 11
        const s = String(stack[sp - 1]);
        if (out.length + s.length > 65536) return finish(11);
        sp--;
        for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (out.length + 1 > 65536) return finish(11);
        out.push(stack[--sp] & 255);
        break;
      case 0x52: // IN: -1 once the input is used up
        stack[sp++] = inPos < input.length ? input[inPos++] : -1;
        break;
      case 0x53: // EXIT: the low byte of v
        return finish(stack[sp - 1] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  let prog;
  try {
    prog = readFileSync(join(I, id, 'program.bin'));
  } catch {
    continue;
  }
  let inp;
  try {
    inp = readFileSync(join(I, id, 'input.bin'));
  } catch {
    inp = Buffer.alloc(0);
  }
  const r = run(prog, inp);
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
