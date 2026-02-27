import { jsx } from "react/jsx-runtime";
import React, { useContext } from "react";
import { EditorContext } from "@leanprover/infoview";

function Link(props) {
  const editor = useContext(EditorContext);

  const handleClick = async () => {
    // Apply the edit
    await editor.api.applyEdit({
      documentChanges: [props.edit].concat(props.otherEdits),
    });

    // Optionally reveal new selection
    if (props.newSelection) {
      await editor.revealLocation({
        uri: props.edit.textDocument.uri,
        range: props.newSelection,
      });
    }
  };

  return jsx("a", {
    className: "link pointer dim",
    title: props.title ?? "",
    onClick: handleClick,
    children: props.children,
  });
}

export default Link;