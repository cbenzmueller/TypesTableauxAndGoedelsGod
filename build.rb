!#/usr/bin/ruby

require 'fileutils'

@pattern = /\(\*\*([\s\S]*)\*\)/
@comment = '--\\<open>\1\\<close>'
@text = 'text\\<open>\1\\<close>'
@gen = 'generated/'
@doc = 'document'

def replace_comments file
	str=""
	lines=File.open(file).readlines
	lines.each{ |line| 
		if line.lstrip.start_with?('(**') then
			str << line.gsub(@pattern,@text)	# one-line text
		else
			str << line.gsub(@pattern,@comment)	# comments 
		end
	}
	str.gsub(@pattern,@text)	# multi-line text
end

def write_file(file, content)
	out_file = File.new(file, 'w')
	out_file.puts(content)
	out_file.close
end

FileUtils.rm_rf @gen
FileUtils.mkdir_p @gen + @doc

Dir.entries('.').select{ |e| File.file?(e) and e.end_with?('.thy') }.each { |f| 
	write_file(@gen + f, replace_comments(f))
}

FileUtils.cp('ROOT', @gen)
FileUtils.cp_r(@doc, @gen)

IO.popen('isabelle build -D ' + @gen)

