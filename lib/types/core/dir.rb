RDL.nowrap :Dir

RDL.rdl_alias :Dir, :'self.[]', :'self.glob'

RDL.type :Dir, 'self.chdir', '(?(String or Pathname)) -> 0'
RDL.type :Dir, 'self.chdir', '(?(String or Pathname)) { (String) -> u } -> u'
RDL.type :Dir, 'self.chroot', '(String) -> 0'
RDL.type :Dir, 'self.delete', '(String) -> 0'
RDL.type :Dir, 'self.entries', '(String, ?Encoding) -> Array<String>'
RDL.type :Dir, 'self.exist?', '(String file) -> %bool'
  # exists? deprecated
RDL.type :Dir, 'self.foreach', '(String dir, ?Encoding) { (String) -> %any } -> nil'
RDL.type :Dir, 'self.foreach', '(String dir, ?Encoding) -> Enumerator<String>'
RDL.type :Dir, 'self.getwd', '() -> String'
RDL.type :Dir, 'self.glob', '(String or Array<String> pattern, ?Fixnum flags) -> Array<String>'
RDL.type :Dir, 'self.glob', '(String or Array<String> pattern, ?Fixnum flags) { (String) -> %any} -> nil'
RDL.type :Dir, 'self.home', '(?String) -> String'
RDL.type :Dir, 'self.mkdir', '(String, ?Integer) -> 0'
RDL.type :Dir, 'self.open', '(String, ?Encoding) -> Dir'
RDL.type :Dir, 'self.open', '(String, ?Encoding) { (Dir) -> u } -> u'
RDL.type :Dir, 'self.pwd', '() -> String'
RDL.type :Dir, 'self.rmdir', '(String) -> 0'
RDL.type :Dir, 'self.unlink', '(String) -> 0'
RDL.type :Dir, :close, '() -> nil'
RDL.type :Dir, :each, '() { (String) -> %any } -> self'
RDL.type :Dir, :each, '() -> Enumerator<String>'
RDL.type :Dir, :fileno, '() -> Integer'
RDL.type :Dir, :initialize, '(String, ?Encoding) -> self'
RDL.type :Dir, :inspect, '() -> String'
RDL.type :Dir, :path, '() -> String or nil'
RDL.type :Dir, :pos, '() -> Integer'
RDL.type :Dir, :pos=, '(Integer) -> Integer'
RDL.type :Dir, :read, '() -> String or nil'
RDL.type :Dir, :rewind, '() -> self'
RDL.type :Dir, :seek, '(Integer) -> self'
RDL.type :Dir, :tell, '() -> Integer'
RDL.type :Dir, :to_path, '() -> String or nil'
