//---------------------------------------------------------------------------
// Copyright 2024, Microsoft Research, Daan Leijen. Tim Whiting.
//
// This is free software; you can redistribute it and/or modify it under the
// terms of the Apache License, Version 2.0. A copy of the License can be
// found in the LICENSE file at the root of this distribution.
//---------------------------------------------------------------------------
// Updated as of 7/23/24: Commit aa9474d
module compiler/common/error
import compiler/common/range
import compiler/common/message
import compiler/common/color-scheme
import compiler/lib/pprint
import std/pretty/printer
import std/os/path

//------------------------------
// Error and warning messages
//------------------------------

// Error messages
pub alias errors = list<error-msg>;

pub alias warnings = errors;

pub type error-msg
  ErrorMsg(
    range: range,
    message: doc,
    severity: error-severity,
    kind: error-kind
  )

// Automatically generated.
// Equality comparison of the `error-msg` type.
pub fun error-msg/(==)(this : error-msg, other : error-msg) : bool
  match (this, other)
    (ErrorMsg(range, message, severity, kind), ErrorMsg(range', message', severity', kind')) -> range == range' && message == message' && severity == severity' && kind == kind'

pub type error-severity
  SevInfo
  SevWarning
  SevError

// Automatically generated.
// Comparison of the `error-severity` type.
pub fun error-severity/cmp(this : error-severity, other : error-severity) : order
  match (this, other)
    (SevInfo, SevInfo) -> Eq
    (SevInfo, _) -> Lt
    (_, SevInfo) -> Gt
    (SevWarning, SevWarning) -> Eq
    (SevWarning, _) -> Lt
    (_, SevWarning) -> Gt
    (SevError, SevError) -> Eq

// Automatically generated.
// Equality comparison of the `error-severity` type.
pub fun error-severity/(==)(this : error-severity, other : error-severity) : bool
  match (this, other)
    (SevInfo, SevInfo) -> True
    (SevWarning, SevWarning) -> True
    (SevError, SevError) -> True
    (_, _) -> False

pub type error-kind
  ErrGeneral
  ErrParse
  ErrStatic
  ErrKind
  ErrType
  ErrBuild
  ErrInternal

// Automatically generated.
// Equality comparison of the `error-kind` type.
pub fun error-kind/(==)(this : error-kind, other : error-kind) : bool
  match (this, other)
    (ErrGeneral, ErrGeneral) -> True
    (ErrParse, ErrParse) -> True
    (ErrStatic, ErrStatic) -> True
    (ErrKind, ErrKind) -> True
    (ErrType, ErrType) -> True
    (ErrBuild, ErrBuild) -> True
    (ErrInternal, ErrInternal) -> True
    (_, _) -> False

pub fun range(errs: errors): range
  errs.map(range).combine

pub fun err/show(err: error-msg, cwd: path = "".path): div string
  err.err/pretty(cwd).show

pub fun errs/show(errs: errors): div string
  errs.errs/pretty.show
    
pub fun is-warning(e: error-msg): bool
  (<=)(e.severity, SevWarning, ?cmp=cmp)

pub fun info-message-kind(d: doc, rng: range, ekind: error-kind = ErrGeneral): error-msg
  ErrorMsg(rng, d, SevInfo, ekind)

pub fun warning-message-kind(d: doc, rng: range, ekind: error-kind = ErrGeneral): error-msg
  ErrorMsg(rng, d, SevWarning, ekind)

pub fun error-message-kind(d: doc, rng: range, ekind: error-kind = ErrGeneral): error-msg
  ErrorMsg(rng, d, SevError, ekind)

pub fun info-message(d: doc, rng: range): _ error-msg
  d.info-message-kind(rng, current-error-kind)

pub fun warning-message(d: doc, rng: range): _ error-msg
  d.warning-message-kind(rng, current-error-kind)

pub fun error-message(d: doc, rng: range): _ error-msg
  d.error-message-kind(rng, current-error-kind)

//---------------------------------
// pretty
//---------------------------------
// `cwd` shortens the displayed path (upstream threads the process's working
// directory in from `Main/Run.hs`); the empty default leaves it untouched,
// which is what a consumer keyed by absolute path (the language server) wants.
pub fun err/pretty(msg: error-msg, cwd: path = "".path): doc
  with color-scheme-default
  msg.pp-error-message(cwd, False)

pub fun errs/pretty(msgs: errors): doc
  with color-scheme-default
  msgs.pp-errors("".path, False)

pub fun pp-error-severity(sev: error-severity, ekind: error-kind): _ doc
  val ekindTxt = match ekind // upstream includes the trailing space in the kind text
    ErrParse -> "parse "
    ErrKind -> "kind "
    ErrType -> "type "
    ErrBuild -> "build "
    ErrInternal -> "internal "
    _ -> ""
  fun header(clr: colorScheme -> color, txt: string)
    text(ekindTxt ++ txt ++ ":").color(clr(colors))
  match sev
    SevError -> header(colorError, "error")
    SevWarning -> header(colorWarning, "warning")
    SevInfo -> header(colorWarning, "info")

pub fun pp-error-message(msg: error-msg, cwd: path, showRangeEnd: bool): _ doc
  (msg.range.pp-range(cwd,showRangeEnd)
  |.| colon |+| msg.severity.pp-error-severity(msg.kind) |+| msg.message
  ).hang(2)

pub fun pp-errors(errs: errors, cwd: path, showRangeEnd: bool): _ doc
  vcat(errs.map(_.pp-error-message(cwd, showRangeEnd)))

pub fun to-warning((range, doc): (range, doc), ekind: error-kind): error-msg
  doc.warning-message-kind(range, ekind)

//--------------------
// Errors Monad
//--------------------

pub effect comp-error
  ctl add-errors(errs: errors): a
  fun add-warnings(w: warnings): ()
  fun add-infos(w: warnings): ()

pub effect val current-error-kind: error-kind

pub fun default-error-kind(f): error-kind
  with val current-error-kind = ErrGeneral
  f()

pub fun msg/add-error(err: error-msg): _ a
  add-errors([err])

pub fun msg/add-warning(msg: error-msg): _ ()
  add-warnings([msg])

pub fun msg/add-info(msg: error-msg): _ ()
  add-infos([msg])

pub fun doc/add-error(rng: range, error: doc): _ a
  add-errors([error-message(error, rng)])

pub fun doc/add-warning(rng: range, warning: doc): _ ()
  add-warnings([warning-message(warning, rng)])

pub fun doc/add-info(rng: range, info: doc): _ ()
  add-infos([info-message(info, rng)])

// check an 'error'
pub fun check-error(f: () -> _ a): either<errors, (a, warnings)>
  var warns := []
  with handler
    final ctl add-errors(errs) Left(errs)
    fun add-warnings(w) warns := w ++ warns
    fun add-infos(w) warns := w ++ warns
    return(x) Right((x, warns))
  f()

pub fun handle-error(f: () -> _ a, h: errors -> _ a): _ a
  with handler
    final ctl add-errors(errs) h(errs)
    fun add-warnings(w) add-warnings(w)
    fun add-infos(w) add-warnings(w)
  f()

pub fun ignore-warnings(f: () -> _ a): _ a
  with handler
    final ctl add-errors(errs) add-errors(errs)
    fun add-warnings(w) ()
    fun add-infos(w) ()
  f()