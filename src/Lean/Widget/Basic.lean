private import Lean.Elab.InfoTree
private import Lean.Message
private import Lean.Server.Rpc.Basic
private import Lean.Server.InfoUtils

namespace Lean.Widget

open Elab Server

deriving instance TypeName for InfoWithCtx
deriving instance TypeName for MessageData
deriving instance TypeName for LocalContext
deriving instance TypeName for Elab.ContextInfo
deriving instance TypeName for Elab.TermInfo

end Lean.Widget
