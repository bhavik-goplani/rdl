class File

  type 'self.absolute_path', '(file: String, dir: ?String) -> abs_file: String'
  type 'self.atime', '(file: String or IO) -> Time'
  type 'self.basename', '(file: String, suffix: ?String) -> base_name: String'
  type 'self.birthtime', '(file: String or IO) -> Time'
  type 'self.blockdev?', '(file: String or IO) -> %bool'
  type 'self.chardev?', '(file: String or IO) -> %bool'
  type 'self.chmod', '(mode: Fixnum, files: *String) -> Fixnum'
  type 'self.chown', '(owner: Fixnum, group: Fixnum, files: *String) -> Fixnum'
  type 'self.ctime', '(file: String or IO) -> Time'
  type 'self.delete', '(files: *String) -> Fixnum'
  type 'self.directory?', '(file: String or IO) -> %bool'
  type 'self.dirname', '(file: String) -> dir: String'
  type 'self.executable?', '(file: String) -> %bool'
  type 'self.executable_real?', '(file: String) -> %bool'
  type 'self.exist?', '(file: String or IO) -> %bool'
  # exists? deprecated
  type 'self.expand_path', '(file: String, dir: ?String) -> abs_file: String'
  type 'self.extname', '(path: String) -> String'
  type 'self.file?', '(file: String or IO) -> %bool'
  type 'self.fnmatch', '(pattern: String, path: String, flags: ?Fixnum) -> %bool'
  rdl_alias :fnmatch?, :fnmatch
  type 'self.ftype', '(file: String) -> String' # TODO: return in set of strings
  type 'self.grpowned?', '(file: String or IO) -> %bool'
  type 'self.identical?', '(file_1: String or IO, file_2: String or IO) -> %bool'
  type 'self.join', '(*String) -> String'
  type 'self.lchmod', '(mode: Fixnum, files: *String) -> Fixnum'
  type 'self.lchown', '(owner: Fixnum, group: Fixnum, files: *String) -> Fixnum'
  type 'self.link', '(old: String, new: String) -> %any' # TODO: Returns 0
  type 'self.lstat', '(file: String) -> File::Stat'
  type 'self.mtime', '(file: String or IO) -> Time'
  type 'self.new', '(file: String, mode: ?String, perm: ?String, opt: ?Fixnum) -> File'
  type 'self.open', '(file: String, mode: ?String, perm: ?String, opt: ?Fixnum) -> File'
  type 'self.open', '(file: String, mode: ?String, perm: ?String, opt: ?Fixnum) { (File) -> t } -> t'
  type 'self.owned?', '(file: String) -> %bool'
  type 'self.path', '(path: String) -> String'
  type 'self.pipe?', '(file: String) -> %bool'
  type 'self.readable?', '(file: String) -> %bool'
  type 'self.readable_real?', '(file: String) -> %bool'
  type 'self.readlink', '(link: String) -> file: String'
  type 'self.readldirpath', '(pathname: String, dir: ?String) -> real_pathname: String'
  type 'self.realpath', '(pathname: String, dir: ?String) -> real_pathname: String'
  type 'self.rename', '(old: String, new: String) -> Fixnum' # TODO: returns 0
  type 'self.setgid?', '(file: String) -> %bool'
  type 'self.setuid?', '(file: String) -> %bool'
  type 'self.size', '(file: String or IO) -> Fixnum'
  type 'self.size?', '(file: String or IO) -> Fixnum or nil'
  type 'self.socket?', '(file: String or IO) -> %bool'
  type 'self.split', '(file: String) -> Array<String>'
  type 'self.stat', '(file: String) -> File::Stat'
  type 'self.sticky?', '(file: String) -> %bool'
  type 'self.symlink', '(old: String, new: String) -> Fixnum' #TODO: returns 0
  type 'self.symlink?', '(file: String) -> %bool'
  type 'self.truncate', '(file: String, Fixnum) -> Fixnum' # TODO returns 0
  type 'self.umask', '(?Fixnum) -> Fixnum'
  rdl_alias :unlink, :delete
  type 'self.utime', '(atime: Time, mtime: Time, files: *String) -> Fixnum'
  type 'self.world_readable?', '(file: String or IO) -> Fixnum or nil'
  type 'self.world_writeable?', '(file: String or IO) -> Fixnum or nil'
  type 'self.writeable?', '(file: String) -> Fixnum or nil'
  type 'self.writeable_real?', '(file: String) -> Fixnum or nil'
  type 'self.zero?', '(file: String or IO) -> Fixnum or nil'

  type :atime, '() -> Time'
  type :birthtime, '() -> Time'
  type :chmod, '(mode: Fixnum) -> Fixnum' # TODO returns 0
  type :chown, '(owner: Fixnum, group: Fixnum) -> Fixnum' # TODO returns 0
  type :ctime, '() -> Time'
  type :flock, '(Fixnum) -> Fixnum or %bool' # todo Fixnum is 0
  type :lstat, '() -> File::Stat'
  type :mtime, '() -> Time'
  type :path, '() -> file: String'
  type :size, '() -> Fixnum'
  rdl_alias :to_path, :path
  type :truncate, '(Fixnum) -> Fixnum' # todo Fixnum is 0
end