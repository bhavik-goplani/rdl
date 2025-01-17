require 'stringio'

class RDL::Util

  SINGLETON_MARKER = "[s]"
  SINGLETON_MARKER_REGEXP = Regexp.escape(SINGLETON_MARKER)
  GLOBAL_NAME = "_Globals" # something that's not a valid class name

  def self.to_class(klass)
    return klass if klass.class == Class
    if has_singleton_marker(klass)
      klass = remove_singleton_marker(klass)
      sing = true
    end
    c = klass.to_s.split("::").inject(Object) { |base, name| base.const_get(name) }
    c = c.singleton_class if sing
    return c
  end

  def self.singleton_class_to_class(cls)
    cls_str = cls.to_s
    cls_str = cls_str.split('(')[0] + '>' if cls_str['(']
    to_class cls_str[8..-2]
  end

  def self.to_class_str(cls)
    cls_str = cls.to_s
    if cls_str.start_with? '#<Class:'
      cls_str = cls_str.split('(')[0] + '>' if cls_str['(']
      cls_str = RDL::Util.add_singleton_marker(cls_str[8..-2])
    end
    cls_str
  end

  def self.has_singleton_marker(klass)
    return (klass.to_s =~ /^#{SINGLETON_MARKER_REGEXP}/)
  end

  def self.remove_singleton_marker(klass)
    if klass.to_s =~ /^#{SINGLETON_MARKER_REGEXP}(.*)/
      return $1
    else
      return nil
    end
  end

  def self.each_leq_constraints(cons)
    cons.each_pair do |k, vs|
      vs.each do |v|
        if v[0] == :lower
          yield v[1], k
        else
          yield k, v[1]
        end
      end
    end
    nil
  end

  def self.count_num_lines(klass, meth)
    ast = RDL::Typecheck.get_ast(klass, meth)
    return nil if ast.nil?
    source = ast.loc.expression.source

    lines = source.lines.delete_if { |line| line.empty? || line.strip.empty? || line.strip.start_with?("#") }
    num_lines_to_subtract = 0
    in_comment = false
    lines.each { |line|
      if line.start_with? "=begin"
        in_comment = true
        num_lines_to_subtract += 1
      elsif line.start_with? "=end"
        in_comment = false
        num_lines_to_subtract += 1
      elsif in_comment
        num_lines_to_subtract += 1
      end
    }
    return lines.size - num_lines_to_subtract
  end
  
  def self.puts_constraints(cons)
    each_leq_constraints(cons) { |a, b| puts "#{a} <= #{b}" }
  end

  def self.add_singleton_marker(klass)
    return SINGLETON_MARKER + klass
  end

  # Duplicate method...
  # Klass should be a string and may have a singleton marker
  # def self.pretty_name(klass, meth)
  #   if klass =~ /^#{SINGLETON_MARKER_REGEXP}(.*)/
  #     return "#{$1}.#{meth}"
  #   else
  #     return "#{klass}##{meth}"
  #   end
  # end

  def self.method_defined?(klass, method)
    begin
      sk = self.to_class klass
      msym = method.to_sym
    rescue NameError
      return false
    end

    return sk.methods.include?(:new) if method == :new

    sk.public_instance_methods(false).include?(msym) or
      sk.protected_instance_methods(false).include?(msym) or
      sk.private_instance_methods(false).include?(msym)
  end

  # Returns the @__rdl_type field of [+obj+]
  def self.rdl_type(obj)
    return (obj.instance_variable_defined?('@__rdl_type') && obj.instance_variable_get('@__rdl_type'))
  end

  def self.rdl_type_or_class(obj)
    return self.rdl_type(obj) || obj.class
  end

  def self.pp_klass_method(klass, meth)
    klass = klass.to_s
    if has_singleton_marker klass
      remove_singleton_marker(klass) + "." + meth.to_s
    else
      klass + "#" + meth.to_s
    end
  end

  def self.silent_warnings
    old_stderr = $stderr
    require "stringio"
    $stderr = StringIO.new
    yield
  ensure
    $stderr = old_stderr
  end
end
