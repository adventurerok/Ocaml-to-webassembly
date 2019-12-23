(module
  (memory (export "memory") 1)
  (global $mem_idx (export "mem_idx") (mut i32) (i32.const 0))
  (func $malloc (export "malloc") (param $size i32) (result i32)
    global.get $mem_idx
    global.get $mem_idx
    local.get $size
    i32.add
    global.set $mem_idx
  )
)
