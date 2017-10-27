import system.io
open io
#check 'a'

#eval 'a'
#eval '\n'
#eval '\\'
variable [io.interface]
#eval put_str ("aaa".str '\\')
#eval put_str $ repr '\n'
#eval put_str $ string.singleton '\n'
#eval put_str ("aaa".str '\'')

#check ['\x7f', '\x00', '\u0000', '\u7fff']
-- ^^ all characters should be pretty-printed using \u escapes

#eval 'α'
#eval 'β'
#eval '\u03B1'
#eval '\u03B2'
