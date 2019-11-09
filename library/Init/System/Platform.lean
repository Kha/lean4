/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import private Init.Data.Nat.Basic

namespace System
namespace Platform

@[extern "lean_system_platform_nbits"]
constant getNumBits : Unit → Nat := arbitrary _

@[extern "lean_system_platform_windows"]
constant getIsWindows : Unit → Bool := arbitrary _

@[extern "lean_system_platform_osx"]
constant getIsOSX : Unit → Bool := arbitrary _

def numBits : Nat := getNumBits ()
def isWindows : Bool := getIsWindows ()
def isOSX : Bool := getIsOSX ()

end Platform
end System
