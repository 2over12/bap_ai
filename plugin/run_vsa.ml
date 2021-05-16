open Core_kernel
open Bap.Std
open Graphlib.Std
open Format
include Self()

let main entry_point proj = ()


module Cmdline = struct
  open Config
  let entry_point = param string "entry_point" ~doc:"Name of the entry function"

  let () = when_ready (fun {get=(!!)} ->
      Project.register_pass' (main !!entry_point ))

  let () = manpage [
      `S "DESCRIPTION";
      `P
        "Checks whether there is an execution path that contains a call
    to the $(v,src) function before a call to the $(v,dst)
    parameter. Outputs a possible (shortest) path that can
    lead to the policy violation."
    ]
end