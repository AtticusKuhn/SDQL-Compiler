#let mathpar(
  numbering: auto,
  row-gutter: 1.2em, // can be set to 'auto'
  column-gutter: 2.5em,
  ..children
) = layout(bounds => {
  // Resolve parameters
  let numbering = if numbering == auto { math.equation.numbering } else { numbering }
  let row-gutter = if row-gutter == auto { par.leading } else { row-gutter.to-absolute() }
  let column-gutter = column-gutter.to-absolute()
  let children = children.pos().map(child => [#child])

  // Spread children into lines
  let widths = children.map(child => measure(child).width)
  let lines = ((children: (), remaining: bounds.width),)
  for (child, width) in children.zip(widths) {
    if (
      child.func() == linebreak or
      (lines.last().remaining - width) / (lines.last().children.len() + 2) < column-gutter
    ){
      lines.push((children: (), remaining: bounds.width))
    }

    if child.func() != linebreak {
      lines.last().children.push(child)
      lines.last().remaining -= width
    }
  }

  // Layout children in math mode for baseline alignment
  par(leading: row-gutter, math.equation(numbering: numbering, block: true,
    for (i, line) in lines.enumerate() {
      let space = h(line.remaining / (line.children.len() + 1))
      par(leading: par.leading, space + line.children.join(space) + space)
      if i != lines.len() - 1 { linebreak() }
    }
  ))
})
