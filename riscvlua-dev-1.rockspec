package = "riscvlua"
version = "dev-1"
source = {
   url = "git+https://github.com/bainchild/riscvlua.git"
}
description = {
   summary = "",
   license = "MIT-0"
}
dependencies = {
   "lua >= 5.1,<= 5.4"
}
build = {
   type = "builtin",
   modules = {
      ["riscvlua.elf"] = "ELF.lua",
      ["riscvlua"] = "init.lua"
   },
   install = {
      bin = {"riscvlua"}
   }
}
