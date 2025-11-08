local little_endian = true
local ptr_size = 4
-- local enable_customint = false
---@diagnostic disable-next-line: access-invisible
local bit32 = bit or bit32 or require("bit32")
-- local bit64,customint = bit64,customint
-- if enable_customint then
--    bit64 = bit64 or require('bit64') -- customint w64 bit library
--    customint = customint or require('customint') -- customint
-- end
local function combine_numbers(...)
   local n = 0
   for i, v in next, { ... } do
      n = bit32.bor(n, bit32.lshift(v, (i - 1) * 8))
   end
   return n
end
--
local function read_byte(s, n)
   if n == nil or n == 1 then
      local char = s:read(1)
      if char then
         return char:byte()
      end
      return nil
   end
   local str, res = s:read(n), {}
   if little_endian then
      for i = 1, n do
         table.insert(res, str:byte(i))
      end
   else
      for i = n, 1, -1 do
         table.insert(res, str:byte(i))
      end
   end
   ---@diagnostic disable-next-line: access-invisible
   return (table.unpack or unpack)(res)
end
local function read_ptr(s)
   return read_byte(s, ptr_size)
end
local function cread_byte(...)
   return combine_numbers(read_byte(...))
end
local function cread_ptr(...)
   return combine_numbers(read_ptr(...))
end
---@return ELF_Header
local function read_elf_header(s)
   little_endian = true
   local class = read_byte(s, 1)
   if class == 1 then
      ptr_size = 4
   elseif class == 2 then
      ptr_size = 8
   end
   -- assert(class==1 or class==2,"Unknown class")
   local endianness = read_byte(s)
   local ei_version = read_byte(s)
   assert(ei_version == 1, "Bad/unsupported version.")
   local abi = read_byte(s)
   local abi_version = read_byte(s)
   read_byte(s, 7) -- padding
   if endianness == 1 then
      little_endian = true
   elseif endianness == 2 then
      little_endian = false
   end
   local filetype = cread_byte(s, 2)
   local machine = cread_byte(s, 2)
   local version = cread_byte(s, 4)
   local entry = cread_ptr(s)
   local phoff = cread_ptr(s)
   local shoff = cread_ptr(s)
   local flags = cread_byte(s, 4)
   local ehsize = cread_byte(s, 2) -- -40
   local _usize = ehsize - 40
   local phentsize, phnum, shentsize, shnum, shstrndx, extra = 0, 0, 0, 0, 0, nil
   -- not sure if there's a better way to do this...
   if _usize >= 2 then
      phentsize = cread_byte(s, 2)
      if _usize >= 4 then
         phnum = cread_byte(s, 2)
         if _usize >= 6 then
            shentsize = cread_byte(s, 2)
            if _usize >= 8 then
               shnum = cread_byte(s, 2)
               if _usize >= 10 then
                  shstrndx = cread_byte(s, 2)
                  if _usize > 10 then
                     extra = read_byte(s, _usize - 10)
                  end
               end
            end
         end
      end
   end
   ---@class ELF_Header
   ---@field Class integer
   ---@field Endianness integer
   ---@field EIVersion integer
   ---@field ABI integer
   ---@field ABIVersion integer
   ---@field Filetype integer
   ---@field Machine integer
   ---@field Version integer
   ---@field Entry integer
   ---@field ProgramHeaderOff integer
   ---@field SectionHeaderOff integer
   ---@field Flags integer
   ---@field HeaderSize integer
   ---@field ProgramHeaderEntrySize integer
   ---@field ProgramHeaderAmount integer
   ---@field SectionHeaderEntrySize integer
   ---@field SectionHeaderAmount integer
   ---@field SectionHeaderNameEntry integer
   ---@field Extra string
   return {
      Class = class,
      Endianness = endianness,
      EIVersion = ei_version,
      ABI = abi,
      ABIVersion = abi_version,
      Filetype = filetype,
      Machine = machine,
      Version = version,
      Entry = entry,
      ProgramHeaderOff = phoff,
      SectionHeaderOff = shoff,
      Flags = flags,
      HeaderSize = ehsize,
      ProgramHeaderEntrySize = phentsize,
      ProgramHeaderAmount = phnum,
      SectionHeaderEntrySize = shentsize,
      SectionHeaderAmount = shnum,
      SectionHeaderNameEntry = shstrndx,
      Extra = extra,
   }
end
-- stylua: ignore start
-- is there a better way than checking size every other line?
---@return ELF_Program
local function read_programht_entry(s,class,size)
   if size%4~=0 then error("Unaligned program entries aren't supported (yet?)") while true do end end
   ---@class ELF_Program
   ---@field _FileLocation integer
   ---@field Type integer
   ---@field Flags integer
   ---@field Offset integer
   ---@field Address integer
   ---@field FileSize integer
   ---@field MemorySize integer
   ---@field Alignment integer
   ---@field Extra integer[]?
   local ret = {_FileLocation=s:seek('cur')}
   if size==0 then return ret end
   ret.Type = cread_byte(s,4);size=size-4
   if size==0 then return ret end
   if class==2 then
      ret.Flags = cread_byte(s,4);size=size-4
      if size==0 then return ret end
   end
   ret.Offset = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.Address = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.PhysicalAddress = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.FileSize = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.MemorySize = cread_ptr(s);size=size-ptr_size
   if class==1 then
      ret.Flags = cread_byte(s,4);size=size-4
   end
   if size==0 then return ret end
   ret.Alignment = cread_ptr(s);size=size-ptr_size
   if size~=0 then
      ret.Extra = {read_byte(s,size)}
   end
   return ret
end
---@return ELF_Section
local function read_sectionht_entry(s,size)
   if size%4~=0 then error("Unaligned section entries aren't supported (yet?)") while true do end end
   ---@class ELF_Section
   ---@field _FileLocation integer
   ---@field NameOffset integer
   ---@field Type integer
   ---@field Flags integer
   ---@field Offset integer
   ---@field VirtualAddress integer
   ---@field Linked integer
   ---@field Info integer
   ---@field Alignment integer
   ---@field EntrySize integer
   ---@field Extra integer[]?
   local ret = {_FileLocation=s:seek('cur')}
   if size==0 then return ret end
   ret.NameOffset = cread_byte(s,4);size=size-4
   if size==0 then return ret end
   ret.Type = cread_byte(s,4);size=size-4
   if size==0 then return ret end
   ret.Flags = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.VirtualAddress = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.Offset = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.Size = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.Linked = cread_byte(s,4);size=size-4
   if size==0 then return ret end
   ret.Info = cread_byte(s,4);size=size-4
   if size==0 then return ret end
   ret.Alignment = cread_ptr(s);size=size-ptr_size
   if size==0 then return ret end
   ret.EntrySize = cread_ptr(s);size=size-ptr_size
   if size~=0 then
      ret.Extra = {read_byte(s,size)}
   end
   return ret
end
-- stylua: ignore end
--- Reads an ELF file from given handle.
-- Given the ret argument, it will reset the file position to the beginning afterwards.
---@param s file
---@param ret boolean
---@return ELF
local function read_elf(s, ret)
   assert(s:read(4) == "\127ELF", "Not an ELF file!")
   local head = read_elf_header(s)
   s:seek("set", head.ProgramHeaderOff)
   local phte = {}
   for _ = 1, head.ProgramHeaderAmount do
      table.insert(phte, read_programht_entry(s, head.Class, head.ProgramHeaderEntrySize))
   end
   s:seek("set", head.SectionHeaderOff)
   local shte = {}
   for _ = 1, head.SectionHeaderAmount do
      table.insert(shte, read_sectionht_entry(s, head.SectionHeaderEntrySize))
   end
   if ret then
      s:seek("set", 0)
   end
   ---@class ELF
   ---@field Header ELF_Header
   ---@field ProgramEntries ELF_Program[]
   ---@field SectionEntries ELF_Section[]
   return {
      Header = head,
      ProgramEntries = phte,
      SectionEntries = shte,
   }
end
return read_elf
