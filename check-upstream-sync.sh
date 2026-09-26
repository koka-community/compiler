#!/bin/zsh
# For each ported .kk file: recorded base commit -> Haskell file -> content diff since, in the
# upstream Haskell compiler checkout (override with KOKA_HS). Baselines come from the
# "Updated as of ...: Commit <hash>" headers in the .kk files; keep both in sync when re-porting.
#
# Uses a CONTENT diff (`git diff --shortstat base..HEAD -- file`), not a commit count: on this
# upstream checkout's history (rebases/squashes happened at least once, e.g. around the dev-uv
# merge) a recorded baseline commit is often not an ancestor of current HEAD, so `git log
# base..HEAD -- file | wc -l` counts unrelated/superseded commits as "behind" even when the
# actual file content is byte-identical (confirmed 2026-08-03: of 87 entries, 70 were reported
# as several-to-dozens of commits behind by the old commit-count method but are in fact
# content-identical). Content diff is the trustworthy signal regardless of history shape.
# Output: kk-file|base-commit|hs-file|status|latest upstream commit touching the file
cd "${KOKA_HS:-$HOME/koka/.worktrees/dev-compiler}" || exit 1
entries=(
"common/color-scheme.kk eb98b61dc src/Common/ColorScheme.hs"
"common/error.kk eb98b61dc src/Common/Error.hs"
"common/failure.kk eb98b61dc src/Common/Failure.hs"
"common/file.kk 336bf9b src/Common/File.hs"
"common/message.kk eb98b61dc src/Common/Message.hs"
"common/name-prim.kk eb98b61dc src/Common/NamePrim.hs"
"common/name.kk eb98b61dc src/Common/Name.hs"
"common/nice.kk eb98b61dc src/Common/IdNice.hs"
"common/parse.kk eb98b61dc src/Syntax/Parse.hs"
"common/range.kk eb98b61dc src/Common/Range.hs"
"common/resume-kind.kk eb98b61dc src/Common/ResumeKind.hs"
"common/syntax.kk eb98b61dc src/Common/Syntax.hs"
"common/id.kk eb98b61dc src/Common/Id.hs"
"common/id.kk eb98b61dc src/Common/IdMap.hs"
"common/id.kk eb98b61dc src/Common/IdSet.hs"
"common/name-collections.kk eb98b61dc src/Common/NameMap.hs"
"common/name-collections.kk eb98b61dc src/Common/NameSet.hs"
"common/name-collections.kk eb98b61dc src/Common/QNameMap.hs"
"core/analysis-match.kk eb98b61dc src/Core/AnalysisMatch.hs"
"kind/kind.kk eb98b61dc src/Kind/Kind.hs"
"kind/repr.kk eb98b61dc src/Kind/Repr.hs"
"lib/scc.kk eb98b61dc src/Lib/Scc.hs"
"lib/trace.kk eb98b61dc src/Lib/Trace.hs"
"static/binding-groups.kk eb98b61dc src/Static/BindingGroups.hs"
"syntax/builders.kk eb98b61dc src/Syntax/Parse.hs"
"syntax/highlight.kk eb98b61dc src/Syntax/Highlight.hs"
"syntax/layout.kk eb98b61dc src/Syntax/Layout.hs"
"syntax/lex.kk eb98b61dc src/Syntax/Lexer.x"
"syntax/lexeme.kk eb98b61dc src/Syntax/Lexeme.hs"
"syntax/parse-type.kk eb98b61dc src/Syntax/Parse.hs"
"syntax/parse.kk eb98b61dc src/Syntax/Parse.hs"
"syntax/pretty.kk eb98b61dc src/Syntax/Pretty.hs"
"syntax/promote.kk eb98b61dc src/Syntax/Promote.hs"
"syntax/range-map.kk eb98b61dc src/Syntax/RangeMap.hs"
"syntax/syntax.kk eb98b61dc src/Syntax/Syntax.hs"
"type/operations.kk eb98b61dc src/Type/Operations.hs"
"type/pretty.kk eb98b61dc src/Type/Pretty.hs"
"type/unify.kk eb98b61dc src/Type/Unify.hs"
# backfilled baselines (approx: upstream commit as of the file's last port date)
"backend/c/box.kk eb98b61dc src/Backend/C/Box.hs"
"backend/c/constructors.kk d3b244c src/Backend/C/FromCore.hs"
"backend/c/dup-drops.kk d3b244c src/Backend/C/FromCore.hs"
"backend/c/expr.kk d3b244c src/Backend/C/FromCore.hs"
"backend/c/from-core.kk d3b244c src/Backend/C/FromCore.hs"
"backend/c/helpers.kk d3b244c src/Backend/C/FromCore.hs"
"core/analysis-cctx.kk eb98b61dc src/Core/AnalysisCCtx.hs"
"core/analysis-resume.kk eb98b61dc src/Core/AnalysisResume.hs"
"core/binding-groups.kk eb98b61dc src/Core/BindingGroups.hs"
"core/borrowed.kk eb98b61dc src/Core/Borrowed.hs"
"core/core.kk eb98b61dc src/Core/Core.hs"
"core/corevar.kk eb98b61dc src/Core/CoreVar.hs"
"core/divergent.kk eb98b61dc src/Core/Divergent.hs"
"core/fun-lift.kk eb98b61dc src/Core/FunLift.hs"
"core/inlines.kk eb98b61dc src/Core/Inlines.hs"
"core/monadic.kk eb98b61dc src/Core/Monadic.hs"
"core/monadic-lift.kk eb98b61dc src/Core/MonadicLift.hs"
"core/open-resolve.kk eb98b61dc src/Core/OpenResolve.hs"
"core/parse.kk eb98b61dc src/Core/Parse.hs"
"core/pretty.kk eb98b61dc src/Core/Pretty.hs"
"core/uniquefy.kk eb98b61dc src/Core/Uniquefy.hs"
"core/unreturn.kk eb98b61dc src/Core/UnReturn.hs"
"core/unroll.kk eb98b61dc src/Core/Unroll.hs"
"kind/assumption.kk eb98b61dc src/Kind/Assumption.hs"
"kind/constructors.kk eb98b61dc src/Kind/Constructors.hs"
"kind/import-map.kk eb98b61dc src/Kind/ImportMap.hs"
"kind/synthesize.kk eb98b61dc src/Kind/Infer.hs"
"kind/infer.kk eb98b61dc src/Kind/Infer.hs"
"kind/infer-effect.kk eb98b61dc src/Kind/InferMonad.hs"
"kind/infer-kind.kk eb98b61dc src/Kind/InferKind.hs"
"kind/newtypes.kk eb98b61dc src/Kind/Newtypes.hs"
"kind/pretty.kk eb98b61dc src/Kind/Pretty.hs"
"kind/synonyms.kk eb98b61dc src/Kind/Synonym.hs"
"kind/unify.kk eb98b61dc src/Kind/Unify.hs"
"type/assumption.kk eb98b61dc src/Type/Assumption.hs"
"type/infer-support.kk eb98b61dc src/Type/Infer.hs"
"type/infer.kk eb98b61dc src/Type/Infer.hs"
"type/infer-effect.kk eb98b61dc src/Type/InferMonad.hs"
"type/infgamma.kk eb98b61dc src/Type/InfGamma.hs"
"type/kind.kk eb98b61dc src/Type/Kind.hs"
"type/type.kk eb98b61dc src/Type/Type.hs"
"type/typevar.kk eb98b61dc src/Type/TypeVar.hs"
"common/unique.kk eb98b61dc src/Common/Unique.hs"
"lib/json.kk eb98b61dc src/Lib/JSON.hs"
"lib/pprint.kk eb98b61dc src/Lib/PPrint.hs"
"lib/printer.kk eb98b61dc src/Lib/Printer.hs"
"platform/config.kk eb98b61dc src/Platform/cpp/Platform/Config.hs"
"static/fixity-resolve.kk eb98b61dc src/Static/FixityResolve.hs"
"syntax/lexer.kk eb98b61dc src/Syntax/Lexer.x"
)
for e in $entries; do
  set -- ${=e}
  kk=$1; base=$2; hs=$3
  if ! git cat-file -e "$base^{commit}" 2>/dev/null; then
    echo "$kk|$base|$hs|BADHASH|"
    continue
  fi
  stat=$(git diff --shortstat "$base"..HEAD -- "$hs")
  if [[ -z "$stat" ]]; then
    n="identical"
  else
    n="DIFF:$(echo "$stat" | grep -oE '[0-9]+ (insertion|deletion)' | grep -oE '^[0-9]+' | awk '{s+=$1} END{print s}') lines"
  fi
  latest=$(git log -1 --format='%h %ad %s' --date=short -- "$hs")
  echo "$kk|$base|$hs|$n|$latest"
done
