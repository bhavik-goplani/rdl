rdl_nowrap :String
type :String, :new, '(?String str) -> String new_str'
type :String, :try_convert, '(Object obj) -> String or nil new_string'
type :String, :%, '(Object) -> String'
type :String, :*, '(Integer) -> String'
type :String, :+, '(String) -> String'
type :String, :<<, '(Object) -> String'
type :String, :<=>, '(String other) -> Integer or nil ret'
type :String, :==, '(%any) -> %bool'
type :String, :===, '(%any) -> %bool'
type :String, :=~, '(Object) -> Integer or nil', wrap: false # Wrapping this messes up $1 etc
type :String, :[], '(Integer, ?Integer) -> String or nil'
type :String, :[], '(Range<Integer> or Regexp) -> String or nil'
type :String, :[], '(Regexp, Integer) -> String or nil'
type :String, :[], '(Regexp, String) -> String or nil'
type :String, :[], '(String) -> String or nil'
type :String, :ascii_only?, '() -> %bool'
type :String, :b, '() -> String'
type :String, :bytes, '() -> Array' # TODO: bindings to parameterized (vars)
type :String, :bytesize, '() -> Integer'
type :String, :byteslice, '(Integer, ?Integer) -> String or nil'
type :String, :byteslice, '(Range<Integer>) -> String or nil'
type :String, :capitalize, '() -> String'
type :String, :capitalize!, '() -> String or nil'
type :String, :casecmp, '(String) -> nil or Integer'
type :String, :center, '(Integer, ?String) -> String'
type :String, :chars, '() -> Array'  #deprecated
type :String, :chomp, '(?String) -> String'
type :String, :chomp!, '(?String) -> String or nil'
type :String, :chop, '() -> String'
type :String, :chop!, '() -> String or nil'
type :String, :chr, '() -> String'
type :String, :clear, '() -> String'
type :String, :codepoints, '() -> Array<Integer>' # TODO
type :String, :codepoints, '() {(?%any) -> %any} -> Array<Integer>' # TODO
type :String, :concat, '(Integer or Object) -> String'
type :String, :count, '(String, *String) -> Integer'
type :String, :crypt, '(String) -> String'
type :String, :delete, '(String, *String) -> String'
type :String, :delete!, '(String, *String) -> String or nil'
type :String, :downcase, '() -> String'
type :String, :downcase!, '() -> String or nil'
type :String, :dump, '() -> String'
type :String, :each_byte, '() {(Integer) -> %any} -> String'
type :String, :each_byte, '() -> Enumerator'
type :String, :each_char, '() {(String) -> %any} -> String'
type :String, :each_char, '() -> Enumerator'
type :String, :each_codepoint, '() {(Integer) -> %any} -> String'
type :String, :each_codepoint, '() -> Enumerator'
type :String, :each_line, '(?String) {(Integer) -> %any} -> String'
type :String, :each_line, '(?String) -> Enumerator'
type :String,  :empty?, '() -> %bool'
# type :String, :encode, '(?Encoding, ?Encoding, *Symbol) -> String' # TODO: fix Hash arg:String,
# type :String, :encode!, '(Encoding, ?Encoding, *Symbol) -> String'
type :String, :encoding, '() -> Encoding'
type :String, :end_with?, '(*String) -> %bool'
type :String, :eql?, '(String) -> %bool'
type :String, :force_encoding, '(String or Encoding) -> String'
type :String, :getbyte, '(Integer) -> Integer or nil'
type :String, :gsub, '(Regexp or String, String) -> String', wrap: false # Can't wrap these:String, , since they mess with $1 etc
type :String, :gsub, '(Regexp or String, Hash) -> String', wrap: false
type :String, :gsub, '(Regexp or String) {(String) -> %any } -> String', wrap: false
type :String, :gsub, '(Regexp or String) ->  Enumerator', wrap: false
type :String, :gsub, '(Regexp or String) -> String', wrap: false
type :String, :gsub!, '(Regexp or String, String) -> String or nil', wrap: false
type :String, :gsub!, '(Regexp or String) {(String) -> %any } -> String or nil', wrap: false
type :String, :gsub!, '(Regexp or String) -> Enumerator', wrap: false
type :String, :hash, '() -> Integer'
type :String, :hex, '() -> Integer'
type :String, :include?, '(String) -> %bool'
type :String, :index, '(Regexp or String, ?Integer) -> Integer or nil'
type :String, :replace, '(String) -> String'
type :String, :insert, '(Integer, String) -> String'
type :String, :inspect, '() -> String'
type :String, :intern, '() -> Symbol'
type :String, :length, '() -> Integer'
type :String, :lines, '(?String) -> Array<String>'
type :String, :ljust, '(Integer, ?String) -> String' # TODO
type :String, :lstrip, '() -> String'
type :String, :lstrip!, '() -> String or nil'
type :String, :match, '(Regexp or String) -> MatchData'
type :String, :match, '(Regexp or String, Integer) -> MatchData'
type :String, :next, '() -> String'
type :String, :next!, '() -> String'
type :String, :oct, '() -> Integer'
type :String, :ord, '() -> Integer'
type :String, :partition, '(Regexp or String) -> Array<String>'
type :String, :prepend, '(String) -> String'
type :String, :reverse, '() -> String'
type :String, :rindex, '(String or Regexp, ?Integer) -> Integer or nil' # TODO
type :String, :rjust, '(Integer, ?String) -> String' # TODO
type :String, :rpartition, '(String or Regexp) -> Array<String>'
type :String, :rstrip, '() -> String'
type :String, :rstrip!, '() -> String'
type :String, :scan, '(Regexp or String) -> Array<String or Array<String>>', wrap: false # :String, Can't wrap or screws up last_match
type :String, :scan, '(Regexp or String) {(*%any) -> %any} -> Array<String or Array<String>>', wrap: false
type :String, :scrub, '(?String) -> String'
type :String, :scrub, '(?String) {(%any) -> %any} -> String'
type :String, :scrub!, '(?String) -> String'
type :String, :scrub!, '(?String) {(%any) -> %any} -> String'
type :String, :set_byte, '(Integer, Integer) -> Integer'
type :String, :size, '() -> Integer'
rdl_alias :String, :slice, :[]
type :String, :slice!, '(Integer, ?Integer) -> String or nil'
type :String, :slice!, '(Range<Integer> or Regexp) -> String or nil'
type :String, :slice!, '(Regexp, Integer) -> String or nil'
type :String, :slice!, '(Regexp, String) -> String or nil'
type :String, :slice!, '(String) -> String or nil'
type :String, :split, '(?(Regexp or String), ?Integer) -> Array<String>'
type :String, :split, '(?Integer) -> Array<String>'
type :String, :squeeze, '(?String) -> String'
type :String, :squeeze!, '(?String) -> String'
type :String, :start_with?, '(* String) -> %bool'
type :String, :strip, '() -> String'
type :String, :strip!, '() -> String'
type :String, :sub, '(Regexp or String, String or Hash) -> String', wrap: false # Can't wrap these, since they mess with $1 etc
type :String, :sub, '(Regexp or String) {(String) -> %any} -> String', wrap: false
type :String, :sub!, '(Regexp or String, String) -> String', wrap: false # TODO: Does this really not allow Hash?
type :String, :sub!, '(Regexp or String) {(String) -> %any} -> String', wrap: false
type :String, :succ, '() -> String'
type :String, :sum, '(?Integer) -> Integer'
type :String, :swapcase, '() -> String'
type :String, :swapcase!, '() -> String or nil'
type :String, :to_c, '() -> Complex'
type :String, :to_f, '() -> Float'
type :String, :to_i, '(?Integer) -> Integer'
type :String, :to_r, '() -> Rational'
type :String, :to_s, '() -> String'
type :String, :to_str, '() -> String'
type :String, :to_sym, '() -> Symbol'
type :String, :tr, '(String, String) -> String'
type :String, :tr!, '(String, String) -> String or nil'
type :String, :tr_s, '(String, String) -> String'
type :String, :tr_s!, '(String, String) -> String or nil'
type :String, :unpack, '(String) -> Array<String>'
type :String, :upcase, '() -> String'
type :String, :upcase!, '() -> String or nil'
type :String, :upto, '(String, ?bool) -> Enumerator'
type :String, :upto, '(String, ?bool) {(String) -> %any } -> String'
type :String, :valid_encoding?, '() -> %bool'