require_relative 'assembler'

module JIT
  class Compiler
    # Utilities to call C functions and interact with the Ruby VM.
    # See: https://github.com/ruby/ruby/blob/master/rjit_c.rb
    C = RubyVM::RJIT::C

    # Metadata for each YARV instruction.
    INSNS = RubyVM::RJIT::INSNS

    # Size of the JIT buffer
    JIT_BUF_SIZE = 1024 * 1024

    STACK = [:r8, :r9, :r10, :r11]

    EC = :rdi
    CFP = :rsi

    Qnil = 0x04
    Qfalse = 0x00
    Qtrue = 0x14
    Zero = 0x01
    One = 0x03

    Branch = Struct.new(:start_addr, :compile)

    # Initialize a JIT buffer. Called only once.
    def initialize
      # Allocate 64MiB of memory. This returns the memory address.
      @jit_buf = C.mmap(JIT_BUF_SIZE)
      # The number of bytes that have been written to @jit_buf.
      @jit_pos = 0
    end

    # Compile a method. Called after --rjit-call-threshold calls.
    def compile(iseq)
      branches = []
      blocks = split_blocks(iseq)
      blocks.each do |block|
        block[:start_addr] = compile_block(iseq, **block, blocks:, branches:)
        if block[:start_index] == 0
          # Write machine code into memory and use it as a JIT function.
          iseq.body.jit_func = block[:start_addr]
        end
      end

      branches.each do |branch|
        with_addr(branch[:start_addr]) do
          asm = Assembler.new
          branch.compile.call(asm)
          write(asm)
        end
      end
    rescue Exception => e
      abort e.full_message
    end

    def compile_block(iseq, start_index:, end_index:, stack_size:, blocks:, branches:)
      # Write machine code to this assembler.
      asm = Assembler.new

      # Iterate over each YARV instruction.
      insn_index = start_index
      while insn_index <= end_index
        insn = INSNS.fetch(C.rb_vm_insn_decode(iseq.body.iseq_encoded[insn_index]))
        case insn.name
        in :putnil
          asm.mov(STACK[stack_size], Qnil)
          stack_size += 1
        in :leave
          asm.add(CFP, C.rb_control_frame_t.size)
          asm.mov([EC, C.rb_execution_context_t.offsetof(:cfp)], CFP)

          asm.mov(:rax, STACK[stack_size - 1])
          asm.ret
        in :putobject_INT2FIX_0_
          asm.mov(STACK[stack_size], Zero)
          stack_size += 1
        in :putobject_INT2FIX_1_
          asm.mov(STACK[stack_size], One)
          stack_size += 1
        in :putobject
          asm.mov(STACK[stack_size], iseq.body.iseq_encoded[insn_index + 1])
          stack_size += 1
        in :opt_plus
          asm.add(STACK[stack_size - 2], STACK[stack_size - 1])
          asm.sub(STACK[stack_size - 2], 1)
          stack_size -= 1
        in :opt_minus
          asm.sub(STACK[stack_size - 2], STACK[stack_size - 1])
          asm.add(STACK[stack_size - 2], 1)
          stack_size -= 1
        in :getlocal_WC_0
          asm.mov(:rax, [CFP, C.rb_control_frame_t.offsetof(:ep)])
          index = iseq.body.iseq_encoded[insn_index + 1]
          asm.mov(STACK[stack_size], [:rax, -C.VALUE.size * index])
          stack_size += 1
        in :opt_lt
          asm.cmp(STACK[stack_size - 2], STACK[stack_size - 1])
          asm.mov(STACK[stack_size - 2], Qfalse)
          asm.mov(:rax, Qtrue)
          asm.cmovl(STACK[stack_size - 2], :rax)
          stack_size -= 1
        in :putself
          asm.mov(STACK[stack_size], [CFP, C.rb_control_frame_t.offsetof(:self)])
          stack_size += 1
        in :opt_send_without_block
          cd = C.rb_call_data.new(iseq.body.iseq_encoded[insn_index + 1])
          callee_iseq = cd.cc.cme_.def.body.iseq.iseqptr
          if callee_iseq.body.jit_func == 0
            compile(callee_iseq)
          end

          argc = C.vm_ci_argc(cd.ci)

          asm.mov(:rax, [CFP, C.rb_control_frame_t.offsetof(:sp)])
          argc.times do |i|
            asm.mov([:rax,  C.VALUE.size * i], STACK[stack_size - argc + i])
          end

          asm.sub(CFP, C.rb_control_frame_t.size)
          asm.mov([EC, C.rb_execution_context_t.offsetof(:cfp)], CFP)

          asm.add(:rax, C.VALUE.size * (argc + 3))
          asm.mov([CFP, C.rb_control_frame_t.offsetof(:sp)], :rax)

          asm.sub(:rax, C.VALUE.size)
          asm.mov([CFP, C.rb_control_frame_t.offsetof(:ep)], :rax)

          asm.mov([CFP, C.rb_control_frame_t.offsetof(:self)], STACK[stack_size - argc - 1])

          STACK.each do |reg|
            asm.push(reg)
          end

          asm.call(callee_iseq.body.jit_func)

          STACK.reverse_each do |reg|
            asm.pop(reg)
          end

          asm.mov(STACK[stack_size - argc - 1], :rax)

          stack_size -= argc
        in :branchunless
          next_index = insn_index + insn.len
          next_block = blocks.find { |block| block[:start_index] == next_index }

          jump_index = next_index + iseq.body.iseq_encoded[insn_index + 1]
          jump_block = blocks.find { |block| block[:start_index] == jump_index }

          asm.test(STACK[stack_size - 1], ~Qnil)
          stack_size -= 1

          branch = Branch.new
          branch.compile = proc do |asm|
            dummy_addr = @jit_buf + JIT_BUF_SIZE
            asm.jz(jump_block.fetch(:start_addr, dummy_addr))
            asm.jmp(next_block.fetch(:start_addr, dummy_addr))
          end
          asm.branch(branch) do
            branch.compile.call(asm)
          end
          branches << branch
        in :nop
          # none
        end
        insn_index += insn.len
      end

      write(asm)
    rescue Exception => e
      abort e.full_message
    end

    def split_blocks(iseq, insn_index: 0, stack_size: 0, split_indexes: [])
      return [] if split_indexes.include?(insn_index)
      split_indexes << insn_index

      block = { start_index: insn_index, end_index: nil, stack_size: }
      blocks = [block]

      while insn_index < iseq.body.iseq_size
        insn = INSNS.fetch(C.rb_vm_insn_decode(iseq.body.iseq_encoded[insn_index]))
        case insn.name
        when :branchunless
          block[:end_index] = insn_index
          stack_size += inc_sp(iseq, insn_index)

          next_index = insn_index + insn.len
          blocks += split_blocks(iseq, insn_index: next_index, stack_size:, split_indexes:)
          blocks += split_blocks(iseq, insn_index: next_index + iseq.body.iseq_encoded[insn_index + 1], stack_size:, split_indexes:)
          break
        when :leave
          block[:end_index] = insn_index
          break
        else
          stack_size += inc_sp(iseq, insn_index)
          insn_index += insn.len
        end
      end

      blocks
    end

    def inc_sp(iseq, insn_index)
      insn = INSNS.fetch(C.rb_vm_insn_decode(iseq.body.iseq_encoded[insn_index]))
      case insn.name
      in :putnil | :putobject_INT2FIX_1_ | :putobject_INT2FIX_0_ | :putobject | :getlocal_WC_0 | :putself
        1
      in :opt_plus | :opt_minus | :opt_lt | :leave | :branchunless
        -1
      in :opt_send_without_block
        cd = C.rb_call_data.new(iseq.body.iseq_encoded[insn_index + 1])
        -C.vm_ci_argc(cd.ci)
      in :nop
        0
      end
    end

    def with_addr(addr)
      jit_pos = @jit_pos
      @jit_pos = addr - @jit_buf
      yield
    ensure
      @jit_pos = jit_pos
    end

    private

    # Write bytes in a given assembler into @jit_buf.
    # @param asm [JIT::Assembler]
    def write(asm)
      jit_addr = @jit_buf + @jit_pos

      # Append machine code to the JIT buffer
      C.mprotect_write(@jit_buf, JIT_BUF_SIZE) # make @jit_buf writable
      @jit_pos += asm.assemble(jit_addr)
      C.mprotect_exec(@jit_buf, JIT_BUF_SIZE) # make @jit_buf executable

      # Dump disassembly if --rjit-dump-disasm
      if C.rjit_opts.dump_disasm
        C.dump_disasm(jit_addr, @jit_buf + @jit_pos).each do |address, mnemonic, op_str|
          puts "  0x#{format("%x", address)}: #{mnemonic} #{op_str}"
        end
        puts
      end

      jit_addr
    end
  end
end
