# Generated by the protocol buffer compiler.  DO NOT EDIT!
# source: hello.proto

import sys
_b=sys.version_info[0]<3 and (lambda x:x) or (lambda x:x.encode('latin1'))
from google.protobuf import descriptor as _descriptor
from google.protobuf import message as _message
from google.protobuf import reflection as _reflection
from google.protobuf import symbol_database as _symbol_database
from google.protobuf import descriptor_pb2
# @@protoc_insertion_point(imports)

_sym_db = _symbol_database.Default()




DESCRIPTOR = _descriptor.FileDescriptor(
  name='hello.proto',
  package='',
  syntax='proto2',
  serialized_pb=_b('\n\x0bhello.proto\"J\n\x05hello\x12\x19\n\x03req\x18\x01 \x01(\x0b\x32\n.hello_reqH\x00\x12\x1b\n\x04repl\x18\x02 \x01(\x0b\x32\x0b.hello_replH\x00\x42\t\n\x07hello_m\"\x1b\n\thello_req\x12\x0e\n\x06period\x18\x01 \x02(\r\"\x1c\n\nhello_repl\x12\x0e\n\x06period\x18\x01 \x02(\r')
)
_sym_db.RegisterFileDescriptor(DESCRIPTOR)




_HELLO = _descriptor.Descriptor(
  name='hello',
  full_name='hello',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='req', full_name='hello.req', index=0,
      number=1, type=11, cpp_type=10, label=1,
      has_default_value=False, default_value=None,
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
    _descriptor.FieldDescriptor(
      name='repl', full_name='hello.repl', index=1,
      number=2, type=11, cpp_type=10, label=1,
      has_default_value=False, default_value=None,
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
  ],
  extensions=[
  ],
  nested_types=[],
  enum_types=[
  ],
  options=None,
  is_extendable=False,
  syntax='proto2',
  extension_ranges=[],
  oneofs=[
    _descriptor.OneofDescriptor(
      name='hello_m', full_name='hello.hello_m',
      index=0, containing_type=None, fields=[]),
  ],
  serialized_start=15,
  serialized_end=89,
)


_HELLO_REQ = _descriptor.Descriptor(
  name='hello_req',
  full_name='hello_req',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='period', full_name='hello_req.period', index=0,
      number=1, type=13, cpp_type=3, label=2,
      has_default_value=False, default_value=0,
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
  ],
  extensions=[
  ],
  nested_types=[],
  enum_types=[
  ],
  options=None,
  is_extendable=False,
  syntax='proto2',
  extension_ranges=[],
  oneofs=[
  ],
  serialized_start=91,
  serialized_end=118,
)


_HELLO_REPL = _descriptor.Descriptor(
  name='hello_repl',
  full_name='hello_repl',
  filename=None,
  file=DESCRIPTOR,
  containing_type=None,
  fields=[
    _descriptor.FieldDescriptor(
      name='period', full_name='hello_repl.period', index=0,
      number=1, type=13, cpp_type=3, label=2,
      has_default_value=False, default_value=0,
      message_type=None, enum_type=None, containing_type=None,
      is_extension=False, extension_scope=None,
      options=None),
  ],
  extensions=[
  ],
  nested_types=[],
  enum_types=[
  ],
  options=None,
  is_extendable=False,
  syntax='proto2',
  extension_ranges=[],
  oneofs=[
  ],
  serialized_start=120,
  serialized_end=148,
)

_HELLO.fields_by_name['req'].message_type = _HELLO_REQ
_HELLO.fields_by_name['repl'].message_type = _HELLO_REPL
_HELLO.oneofs_by_name['hello_m'].fields.append(
  _HELLO.fields_by_name['req'])
_HELLO.fields_by_name['req'].containing_oneof = _HELLO.oneofs_by_name['hello_m']
_HELLO.oneofs_by_name['hello_m'].fields.append(
  _HELLO.fields_by_name['repl'])
_HELLO.fields_by_name['repl'].containing_oneof = _HELLO.oneofs_by_name['hello_m']
DESCRIPTOR.message_types_by_name['hello'] = _HELLO
DESCRIPTOR.message_types_by_name['hello_req'] = _HELLO_REQ
DESCRIPTOR.message_types_by_name['hello_repl'] = _HELLO_REPL

hello = _reflection.GeneratedProtocolMessageType('hello', (_message.Message,), dict(
  DESCRIPTOR = _HELLO,
  __module__ = 'hello_pb2'
  # @@protoc_insertion_point(class_scope:hello)
  ))
_sym_db.RegisterMessage(hello)

hello_req = _reflection.GeneratedProtocolMessageType('hello_req', (_message.Message,), dict(
  DESCRIPTOR = _HELLO_REQ,
  __module__ = 'hello_pb2'
  # @@protoc_insertion_point(class_scope:hello_req)
  ))
_sym_db.RegisterMessage(hello_req)

hello_repl = _reflection.GeneratedProtocolMessageType('hello_repl', (_message.Message,), dict(
  DESCRIPTOR = _HELLO_REPL,
  __module__ = 'hello_pb2'
  # @@protoc_insertion_point(class_scope:hello_repl)
  ))
_sym_db.RegisterMessage(hello_repl)


# @@protoc_insertion_point(module_scope)
