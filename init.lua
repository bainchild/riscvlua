-- This file may look ldoc compatible, but it is not and
-- will generate bad documentation. This is because ldoc is
-- was a pain when I tried to set it up.
local jit = jit ---@diagnostic disable-line: undefined-global
local print = print
local unpack = unpack or table.unpack ---@diagnostic disable-line: access-invisible
local bit = bit or bit32 or require("bit32") ---@diagnostic disable-line: undefined-global, access-invisible
local extract, replace = bit.extract, bit.replace ---@diagnostic disable-line: undefined-field
local default_isa
if not extract then
   --- bit.extract polyfill
   ---@param n number|integer
   ---@param field integer
   ---@param width integer?
   ---@return integer
   local function extract2(n, field, width)
      width = width or 1
      ---@diagnostic disable-next-line: param-type-mismatch
      return bit.band(bit.rshift(n, field), 2 ^ width - 1)
   end
   extract = extract2
end
if not replace then
   --- bit.replace polyfill
   ---@param n number|integer
   ---@param v number|integer
   ---@param field integer
   ---@param width integer?
   ---@return integer
   local function replace2(n, v, field, width)
      local mask = 2 ^ width - 1
      ---@diagnostic disable-next-line: param-type-mismatch
      return bit.bor(bit.lshift(bit.band(v, mask), field), bit.band(n, bit.bnot(mask)))
   end
   replace = replace2
end
-- local clamp = math.clamp or function(n,min,max) return math.min(math.max(n,min),max) end
local dump = false
--- opcode type lookup.
---@internal
---@enum (key) RV_OPT
local op_t = {
   [0] = "I", -- LOAD
   nil, -- LOAD-FP (F)
   nil, -- custom-0
   "I", -- MISC-MEM (fence/Zifencei)
   "I", -- OP-IMM
   "U", -- AUIPC
   nil, -- OP-IMM-32 (RV64)
   nil, -- reserved
   "S", -- STORE
   nil, -- STORE-FP (F)
   nil, -- custom-1
   nil, -- AM0 (Zalrsc)
   "R", -- OP (base/M)
   "U", -- LUI
   nil, -- OP-32 (RV64)
   nil, -- reserved
   nil, -- MADD (F)
   nil, -- MSUB (F)
   nil, -- NMSUB (F)
   nil, -- NMADD (F)
   nil, -- OP-FP (F)
   nil, -- OP-V (V)
   nil, -- custom-2
   nil, -- reserved
   "S", -- BRANCH
   "I", -- JALR
   nil, -- reserved
   "U", -- JAL
   "I", -- SYSTEM (ecall,ebreak/Zicsr)
   nil, -- OP-VE (V)
   nil, -- custom-3
   nil, -- reserved
}
-- dev notes:
-- -1 is the opcode name
-- R is {[funct7]={[funct3]=name}}
-- I is {[funct3]=name}
-- S is {[funct3]=name}
-- U is name

--- opcode name lookup.
-- you are assumed to be indexing
-- this table with knowledge of
-- the instruction's type
---@internal
---@enum (key) RV_OPN
local op_n = {
   [0] = { [-1] = "LOAD", [0] = "lb", "lh", "lw", nil, "lbu", "lhu" },
   nil, -- LOAD-FP (F)
   nil, -- custom-0
   { [-1] = "MISC-MEM", [0] = "fence", "fence.i", "fence.tso" }, -- NOTE TO SELF: THINK OF IT LIKE A "SYNC"
   { [-1] = "OP-IMM", [0] = "addi", "slli", "slti", "sltiu", "xori", "srli", "ori", "andi" },
   "auipc", -- AUIPC
   nil, -- OP-IMM-32 (RV64)
   nil, -- reserved
   { [-1] = "STORE", [0] = "sb", "sh", "sw" },
   nil, -- STORE-FP (F)
   nil, -- custom-1
   nil, -- AM0 (Zalrsc)
   {
      [-1] = "OP",
      [0] = { [0] = "add", "sll", "slt", "sltu", "xor", "srl", "or", "and" },
      { [0] = "mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu" },
      [32] = { [0] = "sub", [5] = "sra" },
   },
   "lui",
   nil, -- OP-32 (RV64)
   nil, -- reserved
   nil, -- MADD (F)
   nil, -- MSUB (F)
   nil, -- NMSUB (F)
   nil, -- NMADD (F)
   nil, -- OP-FP (F)
   nil, -- OP-V (V)
   nil, -- custom-2
   nil, -- reserved
   { [-1] = "BRANCH", [0] = "beq", "bne", nil, nil, "blt", "bge", "bltu", "bgeu" },
   { [-1] = "JALR", [0] = "jalr" },
   nil, -- reserved
   "jal",
   { [-1] = "SYSTEM", [0] = "ecall", "csrrw", "csrrs", "csrrc", nil, "csrrwi", "csrrsi", "csrrci" }, -- ecall is differentiated from ebreak by immediate, which isn't supported in this table
   nil, -- OP-VE (V)
   nil, -- custom-3
   nil, -- reserved
}

--- Decodes two's compliments.
---@param n integer
---@param w integer
---@return number
local function twos(n, w)
   if jit and w == 31 then
      return n
   end -- might?? improve performance
   local s, m = extract(n, w, 1), extract(n, 0, w)
   return (s == 1 and -(2 ^ w - m) or m)
end
-- local function stwo(n,w)
--    local s,m = n<0,bit32.extract(n+2^w,0,w)
--    return bit32.bor(bit32.lshift(s and 1 or 0,w),m)
-- end

--- Sign extension. (bit indicies starting from 1)
---@param n integer
---@param ow integer
---@param w integer
---@return integer
local function extend(n, ow, w)
   if extract(n, ow - 1, 1) == 1 then
      ---@diagnostic disable-next-line: param-type-mismatch
      return bit.bor(n, bit.lshift(tonumber(("1"):rep(w - ow + 1), 2), ow - 1))
   else
      return n
   end
end
local memfuncs_set = false
--- Reads a byte from memory.
---@generic M
---@param memory M
---@param addr integer
---@return integer
local function readu8(memory, addr)
   return memory[addr]
end
--- Writes a byte to memory.
---@generic M
---@param memory M
---@param addr integer
---@param data integer
local function writeu8(memory, addr, data)
   memory[addr] = data
end
--- Reads a short from memory.
---@generic M
---@param memory M
---@param addr integer
---@param big boolean?
---@return integer
local function readu16(memory, addr, big)
   local a, b = memory[addr], memory[addr + 1]
   if big then
      a, b = b, a
   end
   return bit.bor(bit.lshift(b or 0, 8), a or 0)
end
--- Writes a short to memory.
---@generic M
---@param memory M
---@param addr integer
---@param data integer
---@param big boolean?
local function writeu16(memory, addr, data, big)
   if big then
      memory[addr + 1] = bit.band(data, 0xff)
      memory[addr] = bit.band(bit.rshift(data, 8), 0xff)
   else
      memory[addr] = bit.band(data, 0xff)
      memory[addr + 1] = bit.band(bit.rshift(data, 8), 0xff)
   end
end
--- Reads a short from memory.
---@generic M
---@param memory M
---@param addr integer
---@param big boolean?
---@return integer
local function readu32(memory, addr, big)
   local a, b, c, d = memory[addr], memory[addr + 1], memory[addr + 2], memory[addr + 3]
   if big then
      a, b, c, d = d, c, b, a
   end
   return bit.bor(bit.lshift(d or 0, 24), bit.lshift(c or 0, 16), bit.lshift(b or 0, 8), a or 0)
end
--- Writes a short to memory.
---@generic M
---@param memory M
---@param addr integer
---@param data integer
---@param big boolean?
local function writeu32(memory, addr, data, big)
   if big then
      memory[addr + 3] = bit.band(data, 0xff)
      memory[addr + 2] = bit.band(bit.rshift(data, 8), 0xff)
      memory[addr + 1] = bit.band(bit.rshift(data, 16), 0xff)
      memory[addr] = bit.rshift(data, 24)
   else
      memory[addr] = bit.band(data, 0xff)
      memory[addr + 1] = bit.band(bit.rshift(data, 8), 0xff)
      memory[addr + 2] = bit.band(bit.rshift(data, 16), 0xff)
      memory[addr + 3] = bit.rshift(data, 24)
   end
end
--- Writes a quad word (16 bytes) to memory.
-- Used for loading ELF files more efficiently.
-- Does not have endian support because it is not
-- influenced by the RISC-V endian control csr.
---@generic M
---@param memory M
---@param addr integer
---@param a integer
---@param b integer
---@param c integer
---@param d integer
---@param e integer
---@param f integer
---@param g integer
---@param h integer
---@param i integer
---@param j integer
---@param k integer
---@param l integer
---@param m integer
---@param n integer
---@param o integer
---@param p integer
local function writeqword(memory, addr, a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)
   if memfuncs_set then -- if memfuncs were set but writeqword was not, then no other choice...
      -- wonder if loop unrolling applies to lua as an interpreted language...
      writeu8(memory, addr + i, a)
      writeu8(memory, addr + i + 1, b)
      writeu8(memory, addr + i + 2, c)
      writeu8(memory, addr + i + 3, d)
      writeu8(memory, addr + i + 4, e)
      writeu8(memory, addr + i + 5, f)
      writeu8(memory, addr + i + 6, g)
      writeu8(memory, addr + i + 7, h)
      writeu8(memory, addr + i + 8, i)
      writeu8(memory, addr + i + 9, j)
      writeu8(memory, addr + i + 10, k)
      writeu8(memory, addr + i + 11, l)
      writeu8(memory, addr + i + 12, m)
      writeu8(memory, addr + i + 13, n)
      writeu8(memory, addr + i + 14, o)
      writeu8(memory, addr + i + 15, p)
      return
   end
   memory[addr], memory[addr + 1], memory[addr + 2], memory[addr + 3], memory[addr + 4], memory[addr + 5], memory[addr + 6], memory[addr + 7], memory[addr + 8], memory[addr + 9], memory[addr + 10], memory[addr + 11], memory[addr + 12], memory[addr + 13], memory[addr + 14], memory[addr + 15] =
      a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p
end
---@enum RV_MCAUSE
local MCAUSE = {
   instruction_address_misaligned = 0,
   instruction_access_fault = 1,
   illegal_instruction = 2,
   breakpoint = 3,
   load_address_misaligned = 4,
   load_access_fault = 5,
   store_address_misaligned = 6,
   store_access_fault = 7,
   ecall_u = 8,
   ecall_s = 9,
   ecall_m = 11,
   instruction_page_fault = 12,
   load_page_fault = 13,
   store_page_fault = 15,
   double_trap = 16,
   virtual_instruction = 22,
   interrupt_timer_supervisor = bit.bor(5, bit.lshift(1, 30)),
   interrupt_timer_machine = bit.bor(7, bit.lshift(1, 30)),
   interrupt_external_supervisor = bit.bor(9, bit.lshift(1, 30)),
   interrupt_external_machine = bit.bor(11, bit.lshift(1, 30)),
}
---@enum RV_CSR
local CSR = {
   fflags = 1,
   frm = 2,
   fcsr = 3,
   cycle = 0xC00,
   time = 0xC01,
   instret = 0xC02,
   cycleh = 0xC80,
   timeh = 0xC81,
   instreth = 0xC82,
   mvendorid = 0xf11,
   marchid = 0xf12,
   mimpid = 0xf13,
   mhartid = 0xf14,
   mconfigptr = 0xf15,
   mstatus = 0x300,
   misa = 0x301,
   medeleg = 0x302,
   mideleg = 0x303,
   mie = 0x304,
   mtvec = 0x305,
   mcounteren = 0x306,
   mstatush = 0x310,
   medelegh = 0x312,
   mscratch = 0x340,
   mepc = 0x341,
   mcause = 0x342,
   mtval = 0x343,
   mip = 0x344,
   mtinst = 0x34A,
   mtval2 = 0x34B,
   menvcfg = 0x30A,
   menvcfgh = 0x31A,
   mseccfg = 0x747,
   mseccfgh = 0x757,
   mcycle = 0xB00,
   minstret = 0xB02,
   mcycleh = 0xB80,
   minstreth = 0xB82,
   mnscratch = 0x740,
   mnepc = 0x741,
   mncause = 0x742,
   mnstatus = 0x744,
   mcountinhibit = 0x320,
   tselect = 0x7A0,
   satp = 0x180,
   scause = 0x142,
   sepc = 0x141,
   stvec = 0x105,
}
local function binary(n, width)
   local s = ""
   for i = width, 0, -1 do
      s = s .. extract(n, i, 1)
   end
   return s
end
local reg_aliases = { [0] = "zero", "ra", "sp", "gp", "tp" }
for i = 5, 7 do
   reg_aliases[i] = "t" .. (i - 5)
end
for i = 8, 9 do
   reg_aliases[i] = "s" .. (i - 8)
end
for i = 10, 17 do
   reg_aliases[i] = "a" .. (i - 10)
end
for i = 18, 27 do
   reg_aliases[i] = "s" .. (i - 16)
end
for i = 28, 31 do
   reg_aliases[i] = "t" .. (i - 25)
end
local function dumpstate(state)
   local hartid = state.csr[CSR.mhartid] or -1
   print(string.format("[%d] mstatus:  %s", hartid, binary(state.csr[CSR.mstatus], 31)))
   print(string.format("[%d] mstatush: %s", hartid, binary(state.csr[CSR.mstatush], 31)))
   for i = 1, 31 do
      print(string.format("[%d] x%02d%s = %08x", hartid, i, reg_aliases[i] and "(" .. reg_aliases[i] .. ")" or "", state.reg[i] or 0))
   end
   print(string.format("[%d] pc = %08x", hartid, state.reg.pc))
end
local state_utils = {}
---@diagnostic disable-next-line: unused-local
function state_utils:access_csr(idx, read, write, val)
   -- print("BITS 8-11",extract(idx,8,4))
   local level, w = extract(idx, 8, 2), extract(idx, 10, 2) ~= 3
   -- todo: side effects
   if dump then
      print(
         string.format(
            "[%d] csr %x %d %d %s %s",
            self.csr[CSR.mhartid] or -1,
            idx,
            self.permission,
            level,
            write and "writing" or "not-writing",
            w and "writable" or "not-writable"
         )
      )
      if idx == CSR.mtvec and write then
         print(string.format("[%d] MTVEC WRITE %s", self.csr[CSR.mhartid] or -1, binary(val, 31)))
      end
   end
   -- note: no isa check needed here because permission should
   -- never be set to anything but valid values
   if
      self.permission ~= 3
      and (idx == CSR.cycle or idx == CSR.cycleh or idx == CSR.instret or idx == CSR.instreth or idx == CSR.time or idx == CSR.timeh)
   then
      -- check if in U-mode, if it's writing, and then if mcounteren permits it
      if not self:assert(self.permission == 0, MCAUSE.illegal_instruction) then
         return
      end
      if not self:assert(write == false, MCAUSE.illegal_instruction) then
         return
      end
      if (idx == CSR.cycle or idx == CSR.cycleh) and not self:assert(extract(self.csr[CSR.mcounteren], 0, 1) == 1, MCAUSE.illegal_instruction) then
         return
      end
      if
         (idx == CSR.instret or idx == CSR.instreth)
         and not self:assert(extract(self.csr[CSR.mcounteren], 2, 1) == 1, MCAUSE.illegal_instruction)
      then
         return
      end
      if (idx == CSR.time or idx == CSR.timeh) and not self:assert(extract(self.csr[CSR.mcounteren], 1, 1) == 1, MCAUSE.illegal_instruction) then
         return
      end
      return true
   end
   if not self:assert(self.permission >= level, MCAUSE.illegal_instruction) then
      return
   end
   if not self:assert(write == false or w, MCAUSE.illegal_instruction) then
      return
   end
   if not self:assert(write == false or idx ~= CSR.tselect, MCAUSE.illegal_instruction) then
      return
   end
   if write and idx == CSR.mcountinhibit and self.group then
      for i, v in next, self.group do
         if i ~= self then
            v.csr[CSR.mcountinhibit] = replace(v.csr[CSR.mcountinhibit], val, 0, 1)
         end
      end
   end
   if write and idx == CSR.misa then
      if self.isa.writable then
         local ext = bit.band(val, 0xffffffc0) -- everything but top 6 bits (padding+xlen)
         for i = 0, 25 do -- for each extension A-Z, check if it's enabled, if so then enable it if possible. Else, disable it.
            local letter = extract(ext, i)
            local key = string.char(65 + i)
            if letter == 1 then
               ---@diagnostic disable-next-line: need-check-nil
               if not default_isa[key] then
                  ext = bit.bxor(ext, bit.lshift(1, i))
               else
                  self.isa[key] = true
               end
            else
               if self.isa[key] then
                  self.isa[key] = false
               end
            end
         end
         self.csr[CSR.misa] = bit.bor(ext, bit.band(self.csr[CSR.misa], 0x0000003f))
      else
         return
      end
   end
   if read and idx == CSR.tselect then
      self.csr[CSR.tselect] = 0
   end
   return true
end
---@diagnostic disable-next-line: unused-local
function state_utils:trap(reason, into)
   if self.toplevel_trap_handler then
      if self:toplevel_trap_handler(reason, into) then
         return
      end
   end
   if dump then
      print(debug.traceback("TRAP!!!!"), reason, string.format("%08x", self.reg.pc))
      print(string.format("[%d] mstatus:  %s", self.csr[CSR.mhartid] or -1, binary(self.csr[CSR.mstatus], 31)))
      print(string.format("[%d] mstatush: %s", self.csr[CSR.mhartid] or -1, binary(self.csr[CSR.mstatush], 31)))
   end
   into = into or 3
   if
      self.permission < 3 and (reason < 31 and bit.band(self.csr[CSR.medeleg], reason))
      or (reason > 31 and bit.band(self.csr[CSR.medelegh], bit.lshift(1, reason - 31)))
   then -- medeleg is set for this exception
      into = 1
   end
   if into == 3 then
      -- this is fine according the current ratified version
      -- but it fails riscv-arch-tests' privilege ebreak test
      -- self.csr[CSR.mtval] = 0
      self.csr[CSR.mtval] = self.reg.pc

      local mstatus, mstatush = self.csr[CSR.mstatus], self.csr[CSR.mstatush]
      if extract(self.csr[CSR.mstatush] or 0, 10) == 1 then -- M-mode-disable-trap already set!
         -- unexpected trap! extension not implemented, so
         if dump then
            print("Unhandled double-trap on hart " .. (self.csr[CSR.mhartid] or "???"))
            print("Cause is " .. (self.csr[CSR.mcause] or reason or "???") .. " from " .. string.format("%016x", self.csr[CSR.mepc] or 0))
            dumpstate(self)
         end
         self.exit = true
         return nil
      end
      -- todo: lower level interrupts moving up, for now all go to M
      mstatus = replace(mstatus, self.permission, 11, 2) -- set MPP to permission
      mstatus = replace(mstatus, extract(self.csr[CSR.mstatus], 3, 1), 7, 1) -- move MIE to MPIE
      mstatus = bit.bxor(mstatus, bit.lshift(1, 6)) -- set MIE to 0
      mstatush = bit.bor(mstatush, bit.lshift(1, 10)) -- set MDT (M-mode-disable-trap)
      if dump then
         print("MDT SET")
         print(string.format("[%d] mstatus:  %s", self.csr[CSR.mhartid] or -1, binary(mstatus, 31)))
         print(string.format("[%d] mstatush: %s", self.csr[CSR.mhartid] or -1, binary(mstatush, 31)))
      end
      self.csr[CSR.mcause] = reason
      self.csr[CSR.mepc] = self.reg.pc
      self.csr[CSR.mstatus] = mstatus
      self.csr[CSR.mstatush] = mstatush
      self.permission = into
      local mtvec = self.csr[CSR.mtvec]
      local base, mode = bit.band(mtvec, bit.bnot(3)), extract(mtvec, 0, 2)
      if dump then
         print("MTVEC", binary(mtvec, 31))
         print("M-MODE MTVEC MODE IS ", mode)
      end
      if mode == 0 then
         self.reg.pc = base
      elseif mode == 1 then
         self.reg.pc = base + reason * 4
      end
   elseif into == 1 then
      local mstatus = self.csr[CSR.mstatus] or 0
      if extract(mstatus, 24) == 1 then -- S-mode-disable-trap already set!
         -- unexpected trap! extension not implemented, so
         if dump then
            print("Unhandled double-trap on hart " .. (self.csr[CSR.mhartid] or "???"))
            print("Cause is " .. (self.csr[CSR.mcause] or reason or "???") .. " from " .. string.format("%016x", self.csr[CSR.mepc] or 0))
            dumpstate(self)
         end
         self.exit = true
         return nil
      end
      mstatus = replace(mstatus, self.permission > 0 and 1 or 0, 8, 1) -- set SPP to permission
      mstatus = replace(mstatus, extract(mstatus, 1), 5, 1) -- move SIE to SPIE
      mstatus = bit.bxor(mstatus, bit.lshift(1, 1)) -- set SIE to 0
      mstatus = bit.bor(mstatus, bit.lshift(1, 24)) -- set SDT (S-mode-disable-trap)
      if dump then
         print("SDT SET")
         print(string.format("[%d] mstatus(s):  %s", self.csr[CSR.mhartid] or -1, binary(mstatus, 31)))
      end
      self.csr[CSR.scause] = reason
      self.csr[CSR.sepc] = self:real2virt(self.reg.pc)
      self.csr[CSR.mstatus] = mstatus
      self.permission = into
      local stvec = self.csr[CSR.stvec]
      local base, mode = bit.band(stvec, bit.bnot(3)), extract(stvec, 0, 2)
      if dump then
         print("S-MODE STVEC MODE IS ", mode)
      end
      if mode == 0 then
         self.reg.pc = base
      elseif mode == 1 then
         self.reg.pc = base + reason * 4
      end
   end
   if dump then
      print(("TRAP WILL GO TO %08x (for reason %d) WITH PERMISSION %d"):format(self.reg.pc, reason, self.permission))
   end
   self.reg.pc = self.reg.pc - self.inst_len
end
function state_utils:assert(val, err)
   if not val then
      if err == nil then
         error("no error set")
      end
      self:trap(err)
      return nil
   end
   return val
end
function state_utils:real2virt(addr)
   if extract(self.csr[CSR.satp], 31) == 0 then
      return addr
   end
   error("TODO")
end
function state_utils:virt2real(addr)
   if extract(self.csr[CSR.satp], 31) == 0 then
      return addr
   end
   error("TODO")
end
---@diagnostic disable-next-line: unused
---@hidden
function state_utils:access_check(from, to, perm)
   -- TODO: access checking
   perm = perm or self.permission
   -- use bit32.extract(self.csr[csr.mstatus],19,1) for mxr, which makes
   -- executable pages also readable
   return from
end
---
-- rs1 and rs2 are converted to values for every format but I
-- because of the csr instructions using the index as an immediate instead
local opamp = {}
opamp[0] = function(state, funct3, rs1, imm11, rd) -- LOAD I
   rs1 = rs1 ~= 0 and state.reg[rs1] or 0
   if rd == 0 then
      return
   end -- TODO: should this exit early, for exception reasons?
   ---@diagnostic disable-next-line: param-type-mismatch
   local base = bit.band(rs1 + twos(extend(imm11, 12, 32), 31), 0xffffffff)
   local big_endian = false
   local permission = state.permission
   if permission == 3 and extract(state.csr[CSR.mstatus], 17) == 1 then -- MPRV
      permission = extract(state.csr[CSR.mstatus], 11, 2) -- MPP
   end
   if permission == 3 then
      big_endian = extract(state.csr[CSR.mstatush], 4) == 1 -- MBE
      -- print("machine big endian",big_endian)
   elseif permission == 1 then
      big_endian = extract(state.csr[CSR.mstatush], 3) == 1 -- SBE
      -- print("supervisor big endian",big_endian)
   elseif permission == 0 then
      big_endian = extract(state.csr[CSR.mstatus], 5) == 1 -- UBE
      -- print("user big endian",big_endian)
   end
   if permission <= 1 then
      base = state:virt2real(base)
   end
   if funct3 == 0 then -- lb
      local base2 = state:assert(state:access_check(base, base, permission), MCAUSE.load_access_fault)
      if not base2 then
         return
      end
      state.reg[rd] = extend(readu8(state.memory, base2) or 0, 8, 32)
      -- print(string.format("LOAD BYTE %02x FROM %08x INTO REGISTER %d",state.reg[rd],base2,rd))
   elseif funct3 == 1 then -- lh
      local base2 = state:assert(state:access_check(base, base + 1, permission), MCAUSE.load_access_fault)
      if not base2 then
         return
      end
      state.reg[rd] = extend(readu16(state.memory, base2, big_endian), 16, 32)
   elseif funct3 == 2 then -- lw
      local base2 = state:assert(state:access_check(base, base + 3, permission), MCAUSE.load_access_fault)
      if not base2 then
         return
      end
      state.reg[rd] = readu32(state.memory, base2, big_endian)
   elseif funct3 == 4 then -- lbu
      local base2 = state:assert(state:access_check(base, base, permission), MCAUSE.load_access_fault)
      if not base2 then
         return
      end
      state.reg[rd] = readu8(state.memory, base2) or 0
   elseif funct3 == 5 then -- lhu
      local base2 = state:assert(state:access_check(base, base + 1, permission), MCAUSE.load_access_fault)
      if not base2 then
         return
      end
      state.reg[rd] = readu16(state.memory, base2, big_endian)
   else
      return state:assert(false, MCAUSE.illegal_instruction)
   end
end
opamp[3] = function(state, funct3, rs1, imm11, rd) -- MISC-MEM I
   rs1 = rs1 ~= 0 and state.reg[rs1] or 0
   if funct3 == 0 and rd == 0 and rs1 == 0 and extract(imm11, 8, 4) == 0 and extract(imm11, 24, 4) == 0 and extract(imm11, 20, 4) == 0 then -- pause hint
      state.sleep = 60
   else
      if dump then
         print("TODO FENCE")
      end
   end
end
-- split for the same reason as OP and BRANCH
-- jit changes unsigned comparison
local mask_sign_bit = bit.bnot(bit.lshift(1, 31))
if jit then
   opamp[4] = function(state, funct3, rs1, imm11, rd) -- OP-IMM I
      rs1 = rs1 ~= 0 and state.reg[rs1] or 0
      if funct3 == 0 then -- addi
         imm11 = twos(imm11, 11)
         -- print(string.format("addi rs1 %08x + imm11 %s%08x = %08x",rs1,imm11<0 and "-" or "",math.abs(imm11),bit32.band(rs1+imm11,0xffffffff)))
         if imm11 == 0 then
            state.reg[rd] = rs1
         else
            ---@diagnostic disable-next-line: param-type-mismatch
            state.reg[rd] = bit.band(rs1 + imm11, 0xffffffff)
         end
      elseif funct3 == 1 then -- slli
         if not state:assert(extract(imm11, 5, 7) == 0, MCAUSE.illegal_instruction) then
            return
         end
         local shift = extract(imm11, 0, 5)
         state.reg[rd] = bit.band(bit.lshift(rs1, shift), 0xffffffff)
      elseif funct3 == 2 then -- slti
         state.reg[rd] = twos(rs1, 31) < twos(imm11, 11) and 1 or 0
      elseif funct3 == 3 then -- sltiu
         imm11 = extend(imm11, 12, 32)
         local s1, s2 = extract(rs1, 31) == 1, extract(imm11, 31) == 1
         rs1, imm11 = bit.band(rs1, mask_sign_bit), bit.band(imm11, mask_sign_bit) -- trim the sign bit
         local lt = (s2 and not s1)
         if not lt and s1 == s2 then
            lt = rs1 < imm11
         end
         state.reg[rd] = lt and 1 or 0
      elseif funct3 == 4 then -- xori
         state.reg[rd] = bit.bxor(rs1, extend(imm11, 12, 32))
         -- print(("xori %08x x %08x -> %08x"):format(rs1,imm11,state.reg[rd]))
      elseif funct3 == 5 then -- srli/srai
         if not state:assert(extract(imm11, 5, 7) == 32 or extract(imm11, 5, 7) == 0, MCAUSE.illegal_instruction) then
            return
         end
         local shift = extract(imm11, 0, 5)
         state.reg[rd] = (extract(imm11, 10) == 1 and bit.arshift or bit.rshift)(rs1, shift)
      elseif funct3 == 6 then -- ori
         state.reg[rd] = bit.bor(rs1, extend(imm11, 12, 32))
      elseif funct3 == 7 then -- andi
         state.reg[rd] = bit.band(rs1, extend(imm11, 12, 32))
         -- print(("andi %08x x %08x -> %08x"):format(rs1,imm11,state.reg[rd]))
      else
         return state:assert(false, MCAUSE.illegal_instruction)
      end
   end
else
   opamp[4] = function(state, funct3, rs1, imm11, rd) -- OP-IMM I
      rs1 = rs1 ~= 0 and state.reg[rs1] or 0
      if funct3 == 0 then -- addi
         imm11 = twos(imm11, 11)
         -- print(string.format("addi rs1 %08x + imm11 %s%08x = %08x",rs1,imm11<0 and "-" or "",math.abs(imm11),bit32.band(rs1+imm11,0xffffffff)))
         if imm11 == 0 then
            state.reg[rd] = rs1
         else
            ---@diagnostic disable-next-line: param-type-mismatch
            state.reg[rd] = bit.band(rs1 + imm11, 0xffffffff)
         end
      elseif funct3 == 1 then -- slli
         if not state:assert(extract(imm11, 5, 7) == 0, MCAUSE.illegal_instruction) then
            return
         end
         local shift = extract(imm11, 0, 5)
         state.reg[rd] = bit.band(bit.lshift(rs1, shift), 0xffffffff)
      elseif funct3 == 2 then -- slti
         state.reg[rd] = twos(rs1, 31) < twos(imm11, 11) and 1 or 0
      elseif funct3 == 3 then -- sltiu
         state.reg[rd] = rs1 < extend(imm11, 12, 32) and 1 or 0
      elseif funct3 == 4 then -- xori
         state.reg[rd] = bit.bxor(rs1, extend(imm11, 12, 32))
         -- print(("xori %08x x %08x -> %08x"):format(rs1,imm11,state.reg[rd]))
      elseif funct3 == 5 then -- srli/srai
         if not state:assert(extract(imm11, 5, 7) == 32 or extract(imm11, 5, 7) == 0, MCAUSE.illegal_instruction) then
            return
         end
         local shift = extract(imm11, 0, 5)
         state.reg[rd] = (extract(imm11, 10) == 1 and bit.arshift or bit.rshift)(rs1, shift)
      elseif funct3 == 6 then -- ori
         state.reg[rd] = bit.bor(rs1, extend(imm11, 12, 32))
      elseif funct3 == 7 then -- andi
         state.reg[rd] = bit.band(rs1, extend(imm11, 12, 32))
         -- print(("andi %08x x %08x -> %08x"):format(rs1,imm11,state.reg[rd]))
      else
         return state:assert(false, MCAUSE.illegal_instruction)
      end
   end
end
opamp[5] = function(state, rd, imm20) -- AUIPC U
   if rd == 0 then
      return
   end
   local off = twos(imm20, 31)
   ---@diagnostic disable-next-line: param-type-mismatch
   state.reg[rd] = bit.band(state.reg.pc + off, 0xffffffff)
   -- print("AUIPC??",state.reg[rd])
end
opamp[8] = function(state, funct3, rs1, rs2, imm12) -- STORE S
   imm12 = bit.bor(extract(imm12, 7, 5), bit.lshift(extract(imm12, 25, 7), 5))
   local base = bit.band(rs1 + twos(extend(imm12, 12, 32), 31), 0xffffffff)
   local big_endian = false
   local permission = state.permission
   if permission == 3 and extract(state.csr[CSR.mstatus], 17) == 1 then -- MPRV
      permission = extract(state.csr[CSR.mstatus], 11, 2) -- MPP
   end
   if permission == 3 then
      big_endian = extract(state.csr[CSR.mstatush], 4) == 1 -- MBE
      -- print("machine big endian",big_endian)
   elseif permission == 1 then
      big_endian = extract(state.csr[CSR.mstatush], 3) == 1 -- SBE
      -- print("supervisor big endian",big_endian)
   elseif permission == 0 then
      big_endian = extract(state.csr[CSR.mstatus], 5) == 1 -- UBE
      -- print("user big endian",big_endian)
   end
   if permission <= 1 then
      base = state:virt2real(base)
   end
   if funct3 == 0 then -- sb
      if not state:assert(state:access_check(base, base), MCAUSE.store_access_fault) then
         return
      end
      writeu8(state.memory, base, bit.band(rs2, 0xff))
   elseif funct3 == 1 then -- sh
      if not state:assert(state:access_check(base, base + 1), MCAUSE.store_access_fault) then
         return
      end
      writeu16(state.memory, base, rs2, big_endian)
   elseif funct3 == 2 then -- sw
      if not state:assert(state:access_check(base, base + 3), MCAUSE.store_access_fault) then
         return
      end
      -- print("BASE: "..("%x"):format(base))
      -- if base==0x80001000 or base==0x80002000 then print("["..(state.csr[CSR.mhartid] or -1).."] test errorred");state.exit=true end -- FOR riscv-tests
      writeu32(state.memory, base, rs2, big_endian)
   else
      return state:assert(false, MCAUSE.illegal_instruction)
   end
end
-- if true then
--    local ver = tonumber(_VERSION:sub(4))
--    local chunk = string.dump(function() end)
--    if not string.pack then function string.pack() return "" end end
--    print("size_int",(ver < 5.3 and chunk:byte(8) or chunk:byte(16)),#string.pack("J",0))
--    print("size_num",(ver < 5.3 and chunk:byte(11) or chunk:byte(17)),#string.pack("n",0))
--    return
-- end
-- if string.pack is nil, and we're on a platform that doesn't have
-- 64 bit integers, this will cause silent logic errors and will
-- be very hard to trace.
local can_M = string.pack == nil or #string.pack("J", "0") >= 8
-- this is split for the same reason as BRANCH and OP-IMM,
-- unsigned comparison is different on luajit
if jit then
   opamp[12] = function(state, funct3, funct7, rs1, rs2, rd) -- OP R
      if dump then
         print("OP", funct3, funct7)
      end
      if funct3 == 0 then
         rs1, rs2 = twos(rs1, 31), twos(rs2, 31)
         if funct7 == 0 then -- add
            if rd ~= 0 then
               ---@diagnostic disable-next-line: param-type-mismatch
               state.reg[rd] = bit.band(rs1 + rs2, 0xffffffff)
            end
         elseif funct7 == 32 then -- sub
            if rd ~= 0 then
               ---@diagnostic disable-next-line: param-type-mismatch
               state.reg[rd] = bit.band(rs1 - rs2, 0xffffffff)
            end
         else
            return state:assert(false, MCAUSE.illegal_instruction)
         end
      elseif funct3 == 1 then -- sll
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         local shift = extract(rs2, 0, 5)
         if rd ~= 0 then
            state.reg[rd] = bit.band(bit.lshift(rs1, shift), 0xffffffff)
         end
      elseif funct3 == 2 then -- slt
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = rs1 < rs2 and 1 or 0
         end
      elseif funct3 == 3 then -- sltu
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            local s1, s2 = extract(rs1, 31) == 1, extract(rs2, 31) == 1
            rs1, rs2 = bit.band(rs1, mask_sign_bit), bit.band(rs2, mask_sign_bit) -- trim the sign bit
            local lt = (s2 and not s1)
            if not lt and s1 == s2 then
               lt = rs1 < rs2
            end
            state.reg[rd] = lt and 1 or 0
         end
      elseif funct3 == 4 then -- xor
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = bit.bxor(rs1, rs2)
         end
      elseif funct3 == 5 then
         local shift = extract(rs2, 0, 5)
         if funct7 == 0 then -- srl
            if rd ~= 0 then
               state.reg[rd] = bit.rshift(rs1, shift)
            end
         elseif funct7 == 32 then -- sra
            if rd ~= 0 then
               state.reg[rd] = bit.arshift(rs1, shift)
            end
         else
            return state:assert(false, MCAUSE.illegal_instruction)
         end
      elseif funct3 == 6 then -- or
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = bit.bor(rs1, rs2)
         end
      elseif funct3 == 7 then -- and
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = bit.band(rs1, rs2)
         end
      else
         return state:assert(false, MCAUSE.illegal_instruction)
      end
   end
else
   opamp[12] = function(state, funct3, funct7, rs1, rs2, rd) -- OP R
      if dump then
         print("OP", funct3, funct7)
      end
      if funct3 == 0 then
         rs1, rs2 = twos(rs1, 31), twos(rs2, 31)
         if funct7 == 0 then -- add
            if rd ~= 0 then
               ---@diagnostic disable-next-line: param-type-mismatch
               state.reg[rd] = bit.band(rs1 + rs2, 0xffffffff)
            end
         elseif funct7 == 32 then -- sub
            if rd ~= 0 then
               ---@diagnostic disable-next-line: param-type-mismatch
               state.reg[rd] = bit.band(rs1 - rs2, 0xffffffff)
            end
         else
            return state:assert(false, MCAUSE.illegal_instruction)
         end
      elseif funct3 == 1 then -- sll
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         local shift = extract(rs2, 0, 5)
         if rd ~= 0 then
            state.reg[rd] = bit.band(bit.lshift(rs1, shift), 0xffffffff)
         end
      elseif funct3 == 2 then -- slt
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         rs1, rs2 = twos(rs1, 31), twos(rs2, 31)
         if rd ~= 0 then
            state.reg[rd] = rs1 < rs2 and 1 or 0
         end
      elseif funct3 == 3 then -- sltu
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = rs1 < rs2 and 1 or 0
         end
      elseif funct3 == 4 then -- xor
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = bit.bxor(rs1, rs2)
         end
      elseif funct3 == 5 then
         local shift = extract(rs2, 0, 5)
         if funct7 == 0 then -- srl
            if rd ~= 0 then
               state.reg[rd] = bit.rshift(rs1, shift)
            end
         elseif funct7 == 32 then -- sra
            if rd ~= 0 then
               state.reg[rd] = bit.arshift(rs1, shift)
            end
         else
            return state:assert(false, MCAUSE.illegal_instruction)
         end
      elseif funct3 == 6 then -- or
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = bit.bor(rs1, rs2)
         end
      elseif funct3 == 7 then -- and
         if not state:assert(funct7 == 0, MCAUSE.illegal_instruction) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = bit.band(rs1, rs2)
         end
      else
         return state:assert(false, MCAUSE.illegal_instruction)
      end
   end
end
if not can_M then
   print("M extension not provided due to lack of 64 bit integers")
end
-- needs to be fixed(?)
opamp[13] = function(state, rd, imm20) -- LUI U
   if rd == 0 then
      return
   end
   if state.csr[CSR.mhartid] == 0 and dump then
      print(("LUI imm20 %08x"):format(imm20))
   end
   state.reg[rd] = imm20 -- immediate handled by decoding
end
-- these fail the riscv-test-suite when using luajit,
-- because luajit automatically converts to signed integers
-- because it can't guarantee the host will support floats
-- (?)
if jit then
   opamp[24] = function(state, funct3, rs1, rs2, imm12) -- BRANCH S
      -- this needs a refactor
      -- perhaps a long (funct3==0 and rs1==rs2) or (funct3==1 and ...
      imm12 = bit.bor(
         bit.lshift(extract(imm12, 31), 12),
         bit.lshift(extract(imm12, 7), 11),
         bit.lshift(extract(imm12, 25, 6), 5),
         bit.lshift(extract(imm12, 8, 4), 1)
      )
      local prevpc = state.reg.pc
      local off = twos(extend(imm12, 13, 32), 31)
      ---@diagnostic disable-next-line: param-type-mismatch
      local target = bit.band(state.reg.pc + off, 0xffffffff) - 4
      if funct3 == 0 then -- beq
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH EQUAL", rs1, rs2)
         end
         if rs1 == rs2 then
            -- print("BEQ state.isa.C",state.isa.C,target%2,target%4)
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 1 then -- bne
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH NOT EQUAL", rs1, rs2)
         end
         if rs1 ~= rs2 then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 4 then -- blt
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH LOWER THAN", rs1, rs2)
         end
         if rs1 < rs2 then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 5 then -- bge
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH GREATER EQUAL", rs1, rs2)
         end
         if rs1 >= rs2 then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 6 then --bltu
         local s1, s2 = extract(rs1, 31) == 1, extract(rs2, 31) == 1
         rs1, rs2 = bit.band(rs1, mask_sign_bit), bit.band(rs2, mask_sign_bit) -- trim the sign bit
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH LOWER THAN UNSIGNED", rs1, s1, rs2, s2)
         end
         -- first one has highest bit set and other doesn't? fail
         -- second one has highest bit set and other doesn't? success
         -- both have it set or none have it set? check
         local lt = (s2 and not s1)
         if not lt and s1 == s2 then
            lt = rs1 < rs2
         end
         if lt then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 7 then --bgeu
         local s1, s2 = extract(rs1, 31) == 1, extract(rs2, 31) == 1
         rs1, rs2 = bit.band(rs1, mask_sign_bit), bit.band(rs2, mask_sign_bit) -- trim the sign bit
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH GREATER EQUAL UNSIGNED", rs1, s1, rs2, s2)
         end
         -- first one has highest bit set and other doesn't? success
         -- second one has highest bit set and other doesn't? fail
         -- both have it set or none have it set? check
         local gte = (s1 and not s2)
         if not gte and s1 == s2 then
            gte = rs1 >= rs2
         end
         if gte then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      else
         return state:assert(false, MCAUSE.illegal_instruction)
      end
      if state.csr[CSR.mhartid] == 0 and dump then
         print(state.reg.pc ~= prevpc and string.format("BRANCH TAKEN TO %08x (%08x %i)", target + 4, imm12, off) or "BRANCH NOT TAKEN")
      end
   end
else
   opamp[24] = function(state, funct3, rs1, rs2, imm12) -- BRANCH S
      -- this needs a refactor
      -- perhaps a long (funct3==0 and rs1==rs2) or (funct3==1 and ...
      imm12 = bit.bor(
         bit.lshift(extract(imm12, 31), 12),
         bit.lshift(extract(imm12, 7), 11),
         bit.lshift(extract(imm12, 25, 6), 5),
         bit.lshift(extract(imm12, 8, 4), 1)
      )
      local prevpc = state.reg.pc
      local off = twos(extend(imm12, 13, 32), 31)
      ---@diagnostic disable-next-line: param-type-mismatch
      local target = bit.band(state.reg.pc + off, 0xffffffff) - 4
      if funct3 == 0 then -- beq
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH EQUAL", rs1, rs2)
         end
         if rs1 == rs2 then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 1 then -- bne
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH NOT EQUAL", rs1, rs2)
         end
         if rs1 ~= rs2 then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 4 then -- blt
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH LOWER THAN", rs1, rs2)
         end
         if twos(rs1, 31) < twos(rs2, 31) then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 5 then -- bge
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH GREATER EQUAL", rs1, rs2)
         end
         if twos(rs1, 31) >= twos(rs2, 31) then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 6 then --bltu
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH LOWER THAN UNSIGNED", rs1, rs2)
         end
         if rs1 < rs2 then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      elseif funct3 == 7 then --bgeu
         if state.csr[CSR.mhartid] == 0 and dump then
            print("BRANCH GREATER EQUAL UNSIGNED", rs1, rs2)
         end
         if rs1 >= rs2 then
            if not state:assert(target % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
               return
            end -- alignment check
            state.reg.pc = target
         end
      else
         return state:assert(false, MCAUSE.illegal_instruction)
      end
      if state.csr[CSR.mhartid] == 0 and dump then
         print(state.reg.pc ~= prevpc and string.format("BRANCH TAKEN TO %08x (%08x %i)", target + 4, imm12, off) or "BRANCH NOT TAKEN")
      end
   end
end
opamp[25] = function(state, funct3, rs1, imm11, rd) -- JALR I
   rs1 = rs1 ~= 0 and state.reg[rs1] or 0
   if funct3 == 0 then -- jalr
      ---@diagnostic disable-next-line: param-type-mismatch
      local dest = bit.band(rs1 + twos(imm11, 11), 0xfffffffe) -- trim last bit
      if not state:assert(dest % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
         return
      end -- alignment check
      local oldpc = state.reg.pc
      if rd ~= 0 then
         state.reg[rd] = bit.band(state.reg.pc + 4, 0xffffffff)
      end
      -- -4 compensates for the incoming increment
      state.reg.pc = dest - 4
      if state.csr[CSR.mhartid] == 0 and dump then
         print(
            "jalr",
            string.format("%08x", oldpc),
            "->",
            string.format("%08x", state.reg.pc),
            string.format("(%08x,%i)", rs1, twos(imm11, 11)),
            "->",
            string.format("%08x", state.reg[rd] or 0)
         )
      end
   else
      return state:assert(false, MCAUSE.illegal_instruction)
   end
end
opamp[27] = function(state, rd, imm20) -- JAL U
   -- TODO: make this smaller
   local pre_signing = bit.bor(
      bit.lshift(extract(imm20, 31), 20),
      bit.lshift(extract(imm20, 12, 8), 12),
      bit.lshift(extract(imm20, 20), 11),
      bit.lshift(extract(imm20, 25, 6), 5),
      bit.lshift(extract(imm20, 21, 4), 1)
   )
   -- print(binary(pre_signing,31))
   local offset = twos(extend(pre_signing, 21, 32), 31)
   ---@diagnostic disable-next-line: param-type-mismatch
   local dest = bit.band(state.reg.pc + offset, 0xffffffff)
   print("jal", string.format("%08x -> %08x -> %08x (%d) -> %08x", imm20, pre_signing, offset, offset, dest))
   if not state:assert(dest % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
      return
   end -- alignment check
   if rd ~= 0 then
      state.reg[rd] = bit.band(state.reg.pc + 4, 0xffffffff)
   end
   state.reg.pc = dest - 4 -- -4 compensates for the incoming increment
   -- exceptions will be generated on next instruction fetch
end
local riscv_tests
opamp[28] = function(state, funct3, rs1, imm11, rd) -- SYSTEM I
   if funct3 == 0 then -- ecall/ebreak
      if imm11 == 0 then -- ecall
         if dump then
            print("ECALL")
         end
         ---@diagnostic disable-next-line: unnecessary-if
         --- THIS IS ONLY FOR riscv-tests (deprecated precursor to riscv-arch-tests)
         if riscv_tests then
            if state.reg[10] ~= 0 then
               print("[" .. (state.csr[CSR.mhartid] or -1) .. "] test failed: " .. state.reg[10]) -- a0
               dumpstate(state)
            else
               print("[" .. (state.csr[CSR.mhartid] or -1) .. "] test success")
            end
            state.exit = true
         else
            ---
            state:trap(
               (state.permission == 3 and MCAUSE.ecall_m) or (state.permission == 1 and MCAUSE.ecall_s) or (state.permission == 0 and MCAUSE.ecall_u)
            )
            return true
         end
      elseif imm11 == 1 then -- ebreak
         if dump then
            print("EBREAK")
         end
         state:trap(MCAUSE.breakpoint)
         return false, true
      else
         local immpart = extract(imm11, 0, 5)
         local funct7 = extract(imm11, 5, 7)
         if immpart == 2 then -- trap return
            if funct7 == 8 then
               if not state:assert(state.isa.S, MCAUSE.illegal_instruction) then
                  return
               end
               -- print("SRET")
               if not state:assert(state.permission ~= 0, MCAUSE.illegal_instruction) then
                  return
               end
               if not state:assert(state.csr[CSR.sepc] % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
                  return
               end -- alignment check
               local mstatus, mstatush = state.csr[CSR.mstatus], state.csr[CSR.mstatush]
               if state.permission == 3 then
                  mstatush = bit.band(mstatush, bit.bnot(bit.lshift(1, 9))) -- unset MDT (M-mode-disable-trap)
               end
               state.permission = extract(state.csr[CSR.mstatus], 8, 1) -- set permission to spp
               -- if state.permission==0 then
               -- unset sdt in sstatus
               -- end
               mstatus = replace(mstatus, 0, 8, 1) -- set spp to user
               mstatus = replace(mstatus, extract(mstatus, 5, 1), 1, 1) -- move spie to sie
               mstatus = bit.bor(mstatus, bit.lshift(1, 4)) -- set spie to 1
               state.csr[CSR.mstatus] = mstatus
               state.csr[CSR.mstatush] = mstatush
               state.reg.pc = (state.csr[CSR.sepc] or 0) - 4
            elseif funct7 == 24 then
               if dump then
                  print("MRET")
               end
               if not state:assert(state.permission == 3, MCAUSE.illegal_instruction) then
                  return
               end
               if not state:assert(state.csr[CSR.mepc] % (state.isa.C and 2 or 4) == 0, MCAUSE.instruction_address_misaligned) then
                  return
               end -- alignment check
               state.permission = math.max(extract(state.csr[CSR.mstatus], 11, 2), (state.isa.U and 0) or (state.isa.S and 1) or 3) -- set permission to mpp
               local mstatus, mstatush = state.csr[CSR.mstatus], state.csr[CSR.mstatush]
               if state.permission ~= 3 then
                  mstatus = bit.bxor(mstatus, bit.lshift(1, 16)) -- unset mprv
               end
               mstatus = replace(mstatus, (state.isa.U and 0) or (state.isa.S and 1) or 3, 11, 2) -- set mpp to user
               mstatus = replace(mstatus, extract(mstatus, 7, 1), 3, 1) -- move mpie to mie
               mstatus = bit.bor(mstatus, bit.lshift(1, 6)) -- set mpie to 1
               mstatush = bit.band(mstatush, bit.bnot(bit.lshift(1, 10))) -- unset MDT (M-mode-disable-trap)
               if dump then
                  print("MDT UNSET")
                  print(string.format("[%d] mstatus:  %s", state.csr[CSR.mhartid] or -1, binary(state.csr[CSR.mstatus], 31)))
                  print(string.format("[%d] mstatush: %s", state.csr[CSR.mhartid] or -1, binary(state.csr[CSR.mstatush], 31)))
               end
               state.csr[CSR.mstatus] = mstatus
               state.csr[CSR.mstatush] = mstatush
               state.reg.pc = state.csr[CSR.mepc] - 4
            elseif funct7 == 56 then
               -- print("MNRET")
               error("TODO")
            else
               return state:assert(false, MCAUSE.illegal_instruction)
            end
         elseif immpart == 5 and funct7 == 8 then
            -- print("WAIT FOR INTERRUPT")
            state.sleep = 30
         else
            return state:assert(false, MCAUSE.illegal_instruction)
         end
      end
   elseif state.isa.Zicsr then
      local val
      if funct3 > 3 then
         val = rs1
      else
         val = rs1 == 0 and 0 or state.reg[rs1]
      end
      if funct3 == 1 or funct3 == 5 then -- csrrw[i]
         if not state:access_csr(imm11, rd ~= 0, true, val) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = state.csr[imm11] or 0
         end
         state.csr[imm11] = val
      elseif funct3 == 2 or funct3 == 6 then -- csrrs[i]
         if not state:access_csr(imm11, true, val ~= 0, val) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = state.csr[imm11] or 0
         end
         if val ~= 0 then
            state.csr[imm11] = bit.bor(state.csr[imm11] or 0, val)
         end
      elseif funct3 == 3 or funct3 == 7 then -- csrrc[i]
         if not state:access_csr(imm11, true, val ~= 0, val) then
            return
         end
         if rd ~= 0 then
            state.reg[rd] = state.csr[imm11] or 0
         end
         if val ~= 0 then
            state.csr[imm11] = bit.band(state.csr[imm11] or 0, bit.bnot(val))
         end
      else
         return state:assert(false, MCAUSE.illegal_instruction)
      end
   else
      return state:assert(false, MCAUSE.illegal_instruction)
   end
   return false, true -- suppress instret increment
end
---
-- local shlookup = {
--    [0]="NULL";
--    "PROGBITS";
--    "SYMTAB";
--    "STRTAB";
--    "RELA";
--    "HASH";
--    "DYNAMIC";
--    "NOTE";
--    "NOBITS";
--    "REL";
--    "SHLIB";
--    "DYNSYM";
--    [0x0E]="INIT_ARRAY";
--    [0x0F]="FINI_ARRAY";
--    [0x10]="PREINIT_ARRAY";
--    [0x11]="GROUP";
--    [0x12]="SYMTAB_SHNDX";
--    [0x13]="NUM";
-- }
local proglookup = {
   [0] = "NULL",
   "LOAD",
   "DYNAMIC",
   "INTERP",
   "NOTE",
   "SHLIB",
   "PHDR",
   "TLS",
}
---@diagnostic disable-next-line: unused
local function rpad(a, b, c)
   return a .. (c or " "):rep(b - #a)
end
---@diagnostic disable-next-line: unused
local function safe(str)
   return (str:gsub("[^\32-\126]", function(b)
      return "\\" .. string.byte(b)
   end))
end
-- local function read_string(s)
--    local str = ""
--    local char
--    repeat
--       char=s:read(1)
--       str=str..char
--    until char=="\0"
--    return safe(str:sub(1,-2))
--    -- local len = s:read(1):byte()
--    -- return safe(s:read(len))
-- end

local startup_csrs = {
   -- just incase it needs to be hardcoded, this key will stay here
   --                      ABCDEFGHIJKLMNOPQRSTUVWXYZ    padding 32bit
   [CSR.misa] = tonumber(("00000000000000000000000000" .. "0000" .. "10"):reverse(), 2),
   [CSR.mvendorid] = 0,
   [CSR.marchid] = 0,
   -- lua version, ascii for J, ascii for U, or the lua version number
   -- as a byte. (Ex: "Lua 5.1" = 0x51, "Lua 5.2" = 0x52, ...)
   [CSR.mimpid] = (jit and string.byte("J"))
      ---@diagnostic disable-next-line: undefined-global
      or (vector and string.byte("U"))
      or (_VERSION and tonumber("0x" .. _VERSION:gsub("[^%x]", "")))
      or 0x51,
   [CSR.mstatus] = bit.lshift(3, 11),
   [CSR.mstatush] = tonumber("000000000010000000000000000000000", 2), -- MDT is set, unless unset all traps are unexpected and will error
   [CSR.medeleg] = 0,
   [CSR.mideleg] = 0,
   [CSR.mip] = 0,
   [CSR.mie] = 0,
   [CSR.mtvec] = 0x80000000,
   [CSR.mcycle] = 0,
   [CSR.mcycleh] = 0,
   [CSR.time] = 0,
   [CSR.timeh] = 0,
   [CSR.minstret] = 0,
   [CSR.minstreth] = 0,
   [CSR.mscratch] = 0,
   [CSR.mcountinhibit] = 0,
   [CSR.satp] = 0,
}
---@enum (key) RV_ISA
default_isa = {
   C = true,
   I = true,
   S = true,
   U = true,
   Zifencei = true,
   Zicsr = true,
   Zicntr = true,
   Zihintpause = true,
   writable = true,
}
-- local cur_isa = startup_csrs[CSR.misa] -- RV32ICSU
for i = 0, 25 do
   if default_isa[string.char(65 + i)] then -- 65 is A
      ---@diagnostic disable-next-line: param-type-mismatch
      startup_csrs[CSR.misa] = bit.bor(startup_csrs[CSR.misa], bit.lshift(1, i))
   end
end
-- if true then
--    print(string.format("%08x",startup_csrs[CSR.misa]))
--    return
-- end

-- @field mcause RV_MCAUSE
-- @field csr RV_CSR
-- @field startup_csrs {[RV_CSR]: integer|number}
-- @field opcode_handlers {[integer]: function}
-- @field opcode_typemap RV_OPT
-- @field opcode_namemap RV_OPN
-- @field io RV_IO
-- @field set_verbose function
-- @field set_print function
-- @field set_riscv_tests function
-- @field set_memory_functions function
local extra = {
   mcause = MCAUSE,
   csr = CSR,
   startup_csrs = startup_csrs,
   opcode_handlers = opamp,
   opcode_typemap = op_t,
   opcode_namemap = op_n,
}
-- IO functions used by the VM.
-- @class RV_IO
-- @field readu32 function
-- @field readu16 function
-- @field readu8 function
-- @field writeu32 function
-- @field writeu16 function
-- @field writeu8 function
-- @field writeqword function
-- @field twos_compliment function
-- @field sign_extend function
-- @field bit bitlib|bit32lib
-- @field binary function
-- @field extract function
-- @field replace function
--riscv.io =
local read_elf = require("riscvlua.elf")
---@generic M
---@param memory M
---@param file file
local function load_elf(memory, file)
   local elf = read_elf(file)
   assert(elf.Header.ABI == 0, "RISC-V ABI (0) expected, got " .. tostring(elf.Header.ABI))
   assert(elf.Header.Machine == 0xF3, "Expected RISC-V machine (231), got " .. tostring(elf.Header.Machine))
   assert(elf.Header.Class == 1, "64 bit isn't supported (yet)")
   -- print("Sections:")
   -- local paddr = 0
   -- for i,v in pairs(elf.SectionEntries) do
   --    local lname
   --    if sst_off and v.NameOffset then
   --       file:seek('set',sst_off+v.NameOffset)
   --       lname=read_string(file)
   --       if #lname==0 then lname=nil end
   --    end
   --    local name = shlookup[v.Type] or "["..tostring(v.Type).."]"
   --    if v.Size then
   --       print(string.format("   %s%s:\n      0x%x - 0x%x\t->\t0x%x - 0x%x",rpad("("..name..")",15," "),lname or "",v.Offset,v.Offset+v.Size,(v.Address or paddr),(v.Address or v.PhysicalAddress or paddr)+v.Size))
   --       paddr=(v.Address or paddr)+v.Size
   --    else
   --       print(string.format("   %s%s:\n      0x%x\t->\t0x%x",rpad("("..name..")",15," "),lname or "",v.Offset,(v.Address or paddr)))
   --       paddr=(v.Address or paddr)+1
   --    end
   -- end
   -- print("Program entries:")
   local paddr = 0
   for _, v in next, elf.ProgramEntries do
      if v.Type == 1 then
         local name = proglookup[v.Type] or "[" .. tostring(v.Type) .. "]"
         local flags = (bit.band(v.Flags, 1) ~= 0 and "X" or " ")
            .. (bit.band(v.Flags, 2) ~= 0 and "W" or " ")
            .. (bit.band(v.Flags, 3) ~= 0 and "R" or " ")
         if flags == "   " then
            flags = "NIL"
         end
         if v.MemorySize then
            if dump then
               print(
                  string.format(
                     "   %s %s: %04x %04x -> %04x",
                     "(" .. name .. ")",
                     flags,
                     v.Offset,
                     (v.FileSize or v.MemorySize),
                     (v.Address or v.PhysicalAddress or paddr)
                  )
               )
            end
            file:seek("set", v.Offset)
            local siz = v.FileSize or v.MemorySize
            local data = file:read(siz)
            if siz % 16 == 0 then
               for dc = 1, siz, 16 do
                  ---@diagnostic disable-next-line: missing-parameter
                  writeqword(memory, (v.Address or v.PhysicalAddress) + dc - 1, data:byte(dc, dc + 15))
               end
            else
               for dc = 1, siz do
                  writeu8(memory, (v.Address or v.PhysicalAddress) + dc - 1, data:byte(dc))
               end
            end
            ---@diagnostic disable-next-line: assign-type-mismatch
            ---@hidden
            paddr = (v.Address or v.PhysicalAddress or paddr) + siz
         end
      end
   end
   -- print(("Entrypoint %x"):format(elf.Header.Entry or 0))
   return elf.Header.Entry, elf
end
---
-- local top_of_code = exec_start
-- do
--    local f = assert(io.open("memdump.bin","wb"))
--    for i=exec_start,exec_start+0x4000 do
--       f:write(string.char(memory[i] or 0))
--    end
--    f:close()
-- end
-- if true then return end
local function run_hart(state, silent)
   ---@diagnostic disable-next-line: redefined-local
   local dump = silent ~= true and dump
   local len = (extract(readu8(state.memory, state.reg.pc) or 0, 0, 2) == 3 and 4 or 2)
   state.inst_len = len
   -- print(string.format("%08x: %08x",state.reg.pc,readu32(state.memory,state.reg.pc)))
   if not state:assert(state.isa.C or len == 4, MCAUSE.illegal_instruction) then
      return
   end
   local addr = state:assert(state:access_check(state.reg.pc, state.reg.pc + len), MCAUSE.instruction_access_fault)
   if not addr then
      return
   end
   local inst
   if len == 4 then
      inst = readu32(state.memory, addr)
   else
      inst = readu16(state.memory, addr)
   end
   -- print(string.format("%08x:",state.reg.pc),inst and string.format("%08x",inst) or tostring(inst),len)
   local noinc, suppress_instret = false, false
   if inst == 0 then
      state:assert(false, MCAUSE.illegal_instruction)
      return
   else
      if len == 4 then
         local opcode = extract(inst, 2, 5)
         -- print(opcode)
         -- if true then state.exit=true; return end
         local opt = op_t[opcode]
         if opt == "R" then
            local rd, funct3, rs1, rs2, funct7 =
               extract(inst, 7, 5), extract(inst, 12, 3), extract(inst, 15, 5), extract(inst, 20, 5), extract(inst, 25, 7)
            if dump then
               local opname = op_n[opcode] and op_n[opcode][funct7] and op_n[opcode][funct7][funct3] or nil
               print(
                  string.format(
                     "[%d] %08x: %s %d, %d, %d",
                     state.csr[CSR.mhartid] or -1,
                     state.reg.pc,
                     opname or tostring(opcode) .. "_" .. tostring(funct3) .. "_" .. tostring(funct7),
                     rd,
                     rs1,
                     rs2
                  )
               )
            end
            local f = state:assert(opamp[opcode], MCAUSE.illegal_instruction)
            if f then
               noinc, suppress_instret = f(state, funct3, funct7, rs1 == 0 and 0 or state.reg[rs1], rs2 == 0 and 0 or state.reg[rs2], rd)
            end
         elseif opt == "I" then
            local rd, funct3, rs1, imm11 = extract(inst, 7, 5), extract(inst, 12, 3), extract(inst, 15, 5), extract(inst, 20, 12)
            if not (opcode == 4 and funct3 == 0 and rd == 0) then -- nop or hint encoded as addi x0, ...
               if dump then
                  local opname = op_n[opcode][funct3]
                  print(
                     string.format(
                        "[%d] %08x: %s %d, %d, %d",
                        state.csr[CSR.mhartid] or -1,
                        state.reg.pc,
                        opname or tostring(opcode) .. "_" .. tostring(funct3),
                        rd,
                        rs1,
                        imm11
                     )
                  )
               end
               local f = state:assert(opamp[opcode], MCAUSE.illegal_instruction)
               if f then
                  noinc, suppress_instret = f(state, funct3, rs1, imm11, rd)
               end
            end
         elseif opt == "S" then
            local funct3, rs1, rs2, imm12 = extract(inst, 12, 3), extract(inst, 15, 5), extract(inst, 20, 5), bit.band(inst, 0xfe000f80)
            if dump then
               local opname = op_n[opcode][funct3]
               print(
                  string.format(
                     "[%d] %08x: %s %d, %d(%d)",
                     state.csr[CSR.mhartid] or -1,
                     state.reg.pc,
                     opname or tostring(opcode) .. "_" .. tostring(funct3),
                     rs2,
                     rs1,
                     imm12
                  )
               )
            end
            local f = state:assert(opamp[opcode], MCAUSE.illegal_instruction)
            if f then
               noinc = f(state, funct3, rs1 == 0 and 0 or state.reg[rs1], rs2 == 0 and 0 or state.reg[rs2], imm12)
            end
         elseif opt == "U" then
            local rd, imm20 = extract(inst, 7, 5), bit.band(inst, 0xFFFFF000)
            if dump then
               local opname = op_n[opcode]
               print(string.format("[%d] %08x: %s %d, %d", state.csr[CSR.mhartid] or -1, state.reg.pc, opname or tostring(opcode), rd, imm20))
            end
            local f = state:assert(opamp[opcode], MCAUSE.illegal_instruction)
            if f then
               noinc, suppress_instret = f(state, rd, imm20)
            end
         else
            if dump then
               print(string.format("(%d) %08x: ??????????? %d", state.csr[CSR.mhartid] or -1, state.reg.pc, opcode))
            end
            state:assert(false, MCAUSE.illegal_instruction)
         end
      elseif len == 2 then
         local op = extract(inst, 0, 2)
         -- print("c.quadrant:",op)
         if op == 0 then
            local funct3 = extract(inst, 13, 3)
            -- print("c.funct3:",funct3)
            if funct3 == 0 then
               -- c.addi4spn
               local rd = 8 + extract(inst, 2, 3)
               local off1 = extract(inst, 5, 8) * 4
               if dump then
                  print(string.format("[%d] %08x: c.addi4spn x%d, %d", state.csr[CSR.mhartid] or -1, state.reg.pc, rd, off1))
               end
               state.reg[rd] = state.reg[2] + off1
            elseif funct3 == 1 then
               -- c.fld
               if dump then
                  print(string.format("[%d] %08x: c.fld (unimplemented)", state.csr[CSR.mhartid] or -1, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            elseif funct3 == 2 then
               -- c.lw
               local dest = 8 + extract(inst, 2, 3)
               local base = 8 + extract(inst, 7, 3)
               local offset = bit.bor(bit.lshift(extract(inst, 10, 3), 3), extract(inst, 5, 2))
               if dump then
                  print(string.format("[%d] %08x: c.lw x%d, x%d(%d)", state.csr[CSR.mhartid] or -1, state.reg.pc, dest, base, offset))
               end
               local addr2 = (state.reg[base] or 0) + offset * 4
               if not state:assert(state:access_check(addr2, addr2 + 3), MCAUSE.store_access_fault) then
                  return
               end
               state.reg[dest] = readu32(state.memory, addr2)
            elseif funct3 == 3 then
               -- c.flw
               if dump then
                  print(string.format("[%d] %08x: c.flw (unimplemented)", state.csr[CSR.mhartid] or -1, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            elseif funct3 == 5 then
               -- c.fsd
               if dump then
                  print(string.format("[%d] %08x: c.fsd (unimplemented)", state.csr[CSR.mhartid] or -1, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            elseif funct3 == 6 then
               -- c.sw
               local src = 8 + extract(inst, 2, 3)
               local base = 8 + extract(inst, 7, 3)
               local offset = bit.bor(bit.lshift(extract(inst, 10, 3), 3), extract(inst, 5, 2))
               if dump then
                  print(string.format("[%d] %08x: c.sw x%d, x%d(%d)", state.csr[CSR.mhartid] or -1, state.reg.pc, src, base, offset))
               end
               local addr2 = state.reg[base] + offset * 4
               if not state:assert(state:access_check(addr2, addr2 + 3), MCAUSE.store_access_fault) then
                  return
               end
               writeu32(state.memory, addr2, state.reg[src])
            elseif funct3 == 7 then
               -- c.fsw
               if dump then
                  print(string.format("[%d] %08x: c.fsw (unimplemented)", state.csr[CSR.mhartid] or -1, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            else
               state:assert(false, MCAUSE.illegal_instruction)
            end
         elseif op == 1 then
            local funct3 = extract(inst, 13, 3)
            -- print("c.funct3:",funct3)
            if funct3 == 0 then
               -- c.addi
               local imm = bit.bor(bit.lshift(extract(inst, 12, 1), 5), extract(inst, 2, 5))
               local rd = extract(inst, 7, 5)
               if rd ~= 0 then
                  if dump then
                     print(string.format("[%d] %08x: c.addi x%d, %d", state.csr[CSR.mhartid] or -1, state.reg.pc, rd, imm))
                  end
                  state.reg[rd] = (state.reg[rd] or 0) + imm
               else
                  if dump then
                     print(string.format("[%d] %08x: c.nop", state.csr[CSR.mhartid] or -1, state.reg.pc))
                  end
               end
            elseif funct3 == 1 then
               -- c.jal
               -- same as c.j but with link register
               local imm = bit.bor(
                  bit.lshift(extract(inst, 12, 1), 11), -- 11
                  bit.lshift(extract(inst, 8, 1), 10), -- 10
                  bit.lshift(extract(inst, 9, 2), 8), -- 8:9
                  bit.lshift(extract(inst, 6, 1), 7), -- 7
                  bit.lshift(extract(inst, 7, 1), 6), -- 6
                  bit.lshift(extract(inst, 2, 1), 5), -- 5
                  bit.lshift(extract(inst, 11, 1), 4), -- 4
                  bit.lshift(extract(inst, 3, 3), 1) -- 1:3
               )
               local offset = twos(extend(imm, 12, 32), 31)
               if dump then
                  print(string.format("[%d] %08x: c.jal %04x(%d)", state.csr[CSR.mhartid] or -1, state.reg.pc, imm, offset))
               end
               state.reg[1] = state.reg.pc + len
               state.reg.pc = state.reg.pc + offset - 2
            elseif funct3 == 2 then
               -- c.li
               local imm = bit.bor(bit.lshift(extract(inst, 12, 1), 5), extract(inst, 2, 5))
               local rd = extract(inst, 7, 5)
               if dump then
                  print(string.format("[%d] %08x: c.li x%d, %d", state.csr[CSR.mhartid] or -1, state.reg.pc, rd, imm))
               end
               if rd ~= 0 then
                  state.reg[rd] = extend(imm, 6, 32)
               end
            elseif funct3 == 3 then
               local rd = extract(inst, 7, 5)
               if rd == 2 then
                  -- c.addi16sp
                  if dump then
                     print(string.format("[%d] %08x: c.addi16sp (todo)", state.csr[CSR.mhartid] or -1, state.reg.pc))
                  end
               else
                  -- c.lui
                  local imm = bit.lshift(bit.bor(bit.lshift(extract(inst, 12, 1), 5), extract(inst, 2, 5)), 12)
                  if dump then
                     print(string.format("[%d] %08x: c.lui x%d, %d", state.csr[CSR.mhartid] or -1, state.reg.pc, rd, imm))
                     print("after the first", binary(imm, 31), extract(imm, 17, 1))
                  end
                  if rd ~= 0 then
                     local afterthe = extend(imm, 18, 32)
                     state.reg[rd] = afterthe
                     print(string.format("after the extended %08x", afterthe))
                  end
               end
            elseif funct3 == 4 then
               -- c.misc-alu
               if dump then
                  print(string.format("[%d] %08x: c.misc-alu (unimplemented)", state.csr[CSR.mhartid] or -1, state.reg.pc))
               end
            elseif funct3 == 5 then
               -- c.j
               -- offset[11|4|9:8|10|6|7|3:1|5], the monstrosity
               -- from 12 11 10 9  8  7  6  5  4  3  2
               -- to   11 4  9  8  10 6  7  3  2  1  5
               local imm = bit.bor(
                  bit.lshift(extract(inst, 12, 1), 11), -- 11
                  bit.lshift(extract(inst, 8, 1), 10), -- 10
                  bit.lshift(extract(inst, 9, 2), 8), -- 8:9
                  bit.lshift(extract(inst, 6, 1), 7), -- 7
                  bit.lshift(extract(inst, 7, 1), 6), -- 6
                  bit.lshift(extract(inst, 2, 1), 5), -- 5
                  bit.lshift(extract(inst, 11, 1), 4), -- 4
                  bit.lshift(extract(inst, 3, 3), 1) -- 1:3
               )
               local offset = twos(extend(imm, 12, 32), 31)
               if dump then
                  print(string.format("[%d] %08x: c.j %04x(%d)", state.csr[CSR.mhartid] or -1, state.reg.pc, imm, offset))
               end
               state.reg.pc = state.reg.pc + offset - 2
            elseif funct3 == 6 then
               -- c.beqz
               -- offset[7:6|2:1|5]
               local offset = twos(
                  extend(
                     bit.lshift(
                        bit.bor(
                           bit.lshift(extract(inst, 12, 1), 7),
                           bit.lshift(extract(inst, 5, 2), 5),
                           bit.lshift(extract(inst, 2, 1), 4),
                           bit.lshift(extract(inst, 10, 2), 2),
                           extract(inst, 3, 2)
                        ),
                        1
                     ),
                     9,
                     32
                  ),
                  31
               )
               local rs1 = extract(7, 3) + 8
               if dump then
                  print(string.format("BRANCH EQUAL TO ZERO %d", state.reg[rs1]))
               end
               if state.reg[rs1] == 0 then
                  state.reg.pc = state.reg.pc + offset - 2
                  if state.csr[CSR.mhartid] == 0 and dump then
                     print(string.format("BRANCH TAKEN TO %08x (%08x %i)", state.reg.pc, offset, offset))
                  end
               else
                  if state.csr[CSR.mhartid] == 0 and dump then
                     print("BRANCH NOT TAKEN")
                  end
               end
            elseif funct3 == 7 then
               -- c.bnez
               -- same as c.beqz but different
               local offset = twos(
                  extend(
                     bit.lshift(
                        bit.bor(
                           bit.lshift(extract(inst, 12, 1), 7),
                           bit.lshift(extract(inst, 5, 2), 5),
                           bit.lshift(extract(inst, 2, 1), 4),
                           bit.lshift(extract(inst, 10, 2), 2),
                           extract(inst, 3, 2)
                        ),
                        1
                     ),
                     9,
                     32
                  ),
                  31
               )
               local rs1 = extract(7, 3) + 8
               if dump then
                  print(string.format("BRANCH NOT EQUAL TO ZERO %d", state.reg[rs1]))
               end
               if state.reg[rs1] ~= 0 then
                  state.reg.pc = state.reg.pc + offset - 2
                  if state.csr[CSR.mhartid] == 0 and dump then
                     print(string.format("BRANCH TAKEN TO %08x (%08x %i)", state.reg.pc, offset, offset))
                  end
               else
                  if state.csr[CSR.mhartid] == 0 and dump then
                     print("BRANCH NOT TAKEN")
                  end
               end
            else
               state:assert(false, MCAUSE.illegal_instruction)
            end
         elseif op == 2 then
            local funct3 = extract(inst, 13, 3)
            -- print("c.funct3:",funct3)
            if funct3 == 0 then
               -- c.slli
               local shamt = bit.bor(bit.lshift(extract(inst, 12), 6), extract(inst, 2, 5))
               local rd1 = extract(inst, 7, 5)
               if dump then
                  print(string.format("[%d] %08x: c.slli x%d, %04x(%d)", state.csr[CSR.mhartid] or 0, state.reg.pc, rd1, shamt, shamt))
               end
               if rd1 ~= 0 then
                  state.reg[rd1] = bit.lshift(state.reg[rd1] or 0, shamt)
               end
            elseif funct3 == 1 then
               -- c.fldsp
               if dump then
                  print(string.format("[%d] %08x: c.fldsp (unimplemented)", state.csr[CSR.mhartid] or 0, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            elseif funct3 == 2 then
               -- c.lwsp
               local dest = extract(inst, 7, 5)
               local offset = bit.lshift(bit.bor(bit.lshift(extract(inst, 2, 2), 5), bit.lshift(extract(inst, 12, 1), 4), extract(inst, 4, 3)), 2)
               if dump then
                  print(string.format("[%d] %08x: c.lwsp x%d, %08x(%d)", state.csr[CSR.mhartid] or 0, state.reg.pc, dest, offset, offset))
               end
               if dest ~= 0 then
                  state.reg[dest] = state.reg[2] + offset * 4 - 2
               end
            elseif funct3 == 3 then
               -- c.flwsp
               if dump then
                  print(string.format("[%d] %08x: c.flwsp (unimplemented)", state.csr[CSR.mhartid] or 0, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            elseif funct3 == 4 then
               local rs1 = extract(inst, 7, 5)
               local rs2 = extract(inst, 2, 5)
               if extract(inst, 12, 1) == 0 then
                  if rs2 == 0 then
                     -- c.jr
                     if dump then
                        print(string.format("[%d] %08x: c.jr x%d", state.csr[CSR.mhartid] or 0, state.reg.pc, rs1))
                     end
                     state.reg.pc = state.reg[rs1] - 2 or 0
                  else
                     -- c.mv
                     if dump then
                        print(string.format("[%d] %08x: c.mv x%d, x%d", state.csr[CSR.mhartid] or 0, state.reg.pc, rs1, rs2))
                     end
                     if rs1 ~= 0 then
                        state.reg[rs1] = rs2 == 0 and 0 or state.reg[rs2]
                     end
                  end
               else
                  if rs1 == 0 then
                     -- c.ebreak
                     if dump then
                        print(string.format("[%d] %08x: c.ebreak", state.csr[CSR.mhartid] or 0, state.reg.pc))
                        print("C.EBREAK")
                     end
                     state:trap(MCAUSE.breakpoint)
                     suppress_instret = true
                  elseif rs2 == 0 then
                     -- c.jalr
                     if dump then
                        print(string.format("[%d] %08x: c.jalr x%d", state.csr[CSR.mhartid] or 0, state.reg.pc, rs1))
                     end
                     state.reg[1] = state.reg.pc + 2
                     state.reg.pc = state.reg[rs1] - 2
                  else --if rs1~=0 and rs2~=0 then
                     -- c.add
                     if dump then
                        print(string.format("[%d] %08x: c.add (todo)", state.csr[CSR.mhartid] or 0, state.reg.pc))
                     end
                  end
               end
            elseif funct3 == 5 then
               -- c.fsdsp
               if dump then
                  print(string.format("[%d] %08x: c.fsdsp (unimplemented)", state.csr[CSR.mhartid] or 0, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            elseif funct3 == 6 then
               -- c.swsp
               -- offset[5:2|7:6]
               local src = extract(inst, 2, 5)
               local offset = bit.lshift(bit.bor(bit.lshift(extract(inst, 11, 2), 4), extract(inst, 7, 4)), 2)
               local base = state.reg[2] + offset
               if dump then
                  print(string.format("[%d] %08x: c.swsp x%d, %08x(%d)", state.csr[CSR.mhartid] or 0, state.reg.pc, src, offset, offset))
               end
               if not state:assert(state:access_check(base, base + 3), MCAUSE.store_access_fault) then
                  return
               end
               writeu32(state.memory, base, state.reg[src] or 0)
            elseif funct3 == 7 then
               -- c.fswsp
               if dump then
                  print(string.format("[%d] %08x: c.fswsp (unimplemented)", state.csr[CSR.mhartid] or 0, state.reg.pc))
               end
               state:assert(false, MCAUSE.illegal_instruction)
            else
               state:assert(false, MCAUSE.illegal_instruction)
            end
         end
      end
      state.reg.pc = state.reg.pc + len
   end
   return noinc, suppress_instret
end
--- Creates a new hart.
-- Optionally associates with a core for synchronization.
---@generic M
---@param memory M
---@param core RV_Core?
---@return RV_Hart
local function new_hart(memory, core)
   --- Class representing a single hart.
   ---@class RV_Hart
   ---@field reg integer[31]
   ---@field freg number[32]
   ---@field csr {[RV_CSR]: integer|number}
   ---@field isa {[RV_ISA]: boolean}
   ---@field memory M
   ---@field permission integer
   ---@field exit boolean
   ---@field sleep integer
   ---@field kill_timer integer
   ---@field kill_timeout integer
   ---@field lastpc integer
   ---@field group RV_Core?
   local hart = {
         -- stylua: ignore start
         reg = {
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,
            pc = core and core.exec_start or 0x800000,
         },
         freg = {
            [0]=0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
            0,0,0,0,
         },
      -- stylua: ignore end
      csr = (function()
         local new = {}
         for i, v in next, startup_csrs do
            new[i] = v
         end
         return new
      end)(),
      isa = (function()
         local new = {}
         for i, v in next, default_isa do
            new[i] = v
         end
         return new
      end)(),
      memory = memory,
      permission = 3,
      exit = false,
      sleep = 20,
      kill_timer = 0,
      kill_timeout = 100,
      lastpc = 0,
      group = core,
   }
   return setmetatable(hart, { __index = state_utils })
end
--- Steps all of the harts in a core once.
-- Returns true if all of the harts have exited.
-- By default, this will only happen from a 1 instruction loop,
-- causing the hart to be killed.
-- Includes management of:
-- - Zicsr counters
-- - infinite loop detection
-- - Zihintpause
-- - Atomics
---@param core RV_Core
---@return boolean?
local function run_core(core)
   core.deltas = core.deltas + (os.time() - core.last)
   local exited = 0
   for _, v in next, core.harts do
      if v.sleep > 0 then
         v.sleep = v.sleep - 1
         -- print("SLEEP",v.sleep)
         -- if v.sleep==0 then print("SLEEP EXPIRED") end
      else
         local noinc, suppress_instret = run_hart(v, v.kill_timeout ~= 100)
         if v.kill_timer == 10 then
            if dump then
               print(string.format("[%d] hart terminated from timeout", v.csr[CSR.mhartid] or -1))
            end
            v.exit = true
         end
         if v.exit then
            exited = exited + 1
            -- dumpregs(v)
         elseif not noinc then
            local csr = v.csr
            -- kill timeout decrements every time pc is the same as last cycle, when the hart is not sleeping
            -- when it reaches 0, it is reset and the hart is put to sleep for 300 cycles
            -- when this happens 10 times, the hart is terminated
            if v.lastpc ~= v.reg.pc then
               v.kill_timeout = 100
               v.kill_timer = 0
            else
               v.kill_timeout = v.kill_timeout - 1
               if v.kill_timeout == 0 then
                  v.kill_timeout = 50
                  v.kill_timer = v.kill_timer + 1
                  v.sleep = 200
                  if v.kill_timer == 3 then
                     print(string.format("[%d] hart is in a loop", csr[CSR.mhartid] or -1))
                  end
               end
            end
            if v.isa.Zicntr then
               local countinhibit = csr[CSR.mcountinhibit]
               if extract(countinhibit, 0, 1) == 0 then
                  local mcycle, mcycleh = CSR.mcycle, CSR.mcycleh
                  ---@diagnostic disable-next-line: param-type-mismatch
                  csr[mcycle] = bit.band(csr[mcycle] + 1, 0xffffffff)
                  if csr[mcycle] == 0 then
                     ---@diagnostic disable-next-line: param-type-mismatch
                     csr[mcycleh] = bit.band(csr[mcycleh] + 1, 0xffffffff)
                  end
               end
               if extract(countinhibit, 2, 1) == 0 and not suppress_instret then
                  local minstret, minstreth = CSR.minstret, CSR.minstreth
                  ---@diagnostic disable-next-line: param-type-mismatch
                  csr[minstret] = bit.band(csr[minstret] + 1, 0xffffffff)
                  if csr[minstret] == 0 then
                     ---@diagnostic disable-next-line: param-type-mismatch
                     csr[minstreth] = bit.band(csr[minstreth] + 1, 0xffffffff)
                  end
               end
               if core.deltas >= 1 then
                  local time, timeh = CSR.time, CSR.timeh
                  ---@diagnostic disable-next-line: param-type-mismatch
                  csr[time] = bit.band(math.floor(csr[time] + core.deltas), 0xffffffff)
                  if csr[time] == 0 then
                     ---@diagnostic disable-next-line: param-type-mismatch
                     csr[timeh] = bit.band(csr[timeh] + 1, 0xffffffff)
                  end
               end
            end
            v.lastpc = v.reg.pc
         end
      end
   end
   if exited == #core.harts then
      return true
   end
   if core.deltas >= 1 then
      core.deltas = 0
   end
   -- os.execute("sleep .1")
end
--- Creates a RV_Core for managing multiple harts
---@generic M
---@param harts integer?
---@param elf file?
---@param mem M
---@return RV_Core, ELF?
local function new_core(harts, elf, mem)
   ---@class RV_Core
   ---@field harts RV_Hart[]
   ---@field exec_start integer
   ---@field last number
   ---@field deltas number
   local core = {
      harts = {},
      memory = mem or {},
      exec_start = 0x8000000,
      last = os.time(),
      deltas = 0,
   }
   if elf then
      core.exec_start, elf = load_elf(core.memory, elf)
   end
   for i = 1, harts or 1 do
      local hart = new_hart(core.memory, core)
      hart.csr[CSR.mhartid] = i - 1
      table.insert(core.harts, hart)
   end
   return core, elf
end

---@export
return {
   read_elf = read_elf,
   load_elf = load_elf,
   create_core = new_core,
   create_hart = new_hart,
   run_core = run_core,
   run_hart = run_hart,
   dump_hart = dumpstate,
   set_verbose = function(verbose)
      dump = verbose
   end,
   set_print = function(printf)
      print = printf
   end,
   set_riscv_tests = function(test)
      riscv_tests = test
   end,
   set_memory_functions = function(r, w)
      readu8, readu16, readu32 = unpack(r)
      writeu8, writeu16, writeu32 = unpack(w)
      if w[4] then
         writeqword = w[4]
      end
      memfuncs_set = true
   end,
   io = {
      -- Used to grab the upvalue for the `readu32` function.
      ---@return function
      readu32 = function()
         return readu32
      end,
      -- Used to grab the upvalue for the `readu16` function.
      ---@return function
      readu16 = function()
         return readu16
      end,
      -- Used to grab the upvalue for the `readu8` function.
      ---@return function
      readu8 = function()
         return readu8
      end,
      -- Used to grab the upvalue for the `writeu32` function.
      ---@return function
      writeu32 = function()
         return writeu32
      end,
      -- Used to grab the upvalue for the `writeu16` function.
      ---@return function
      writeu16 = function()
         return writeu16
      end,
      -- Used to grab the upvalue for the `writeu8` function.
      ---@return function
      writeu8 = function()
         return writeu8
      end,
      -- Used to grab the upvalue for the `writeqword` function.
      ---@return function
      writeqword = function()
         return writeqword
      end,
      -- Twos compliment function. Provided for convenience.
      twos_compliment = twos,
      -- Sign extension function. Provided for convenience.
      sign_extend = extend,
      -- Bit library used by the VM.
      bit = bit,
      -- Binary conversion function. Used for debugging.
      binary = binary,
      -- Bitwise extraction library used by the VM.
      extract = extract,
      -- Bitwise replacement library used by the VM.
      replace = replace,
   },
   extra = extra,
}
