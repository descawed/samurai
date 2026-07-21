'use strict';

const vscode = require('vscode');
const fs = require('fs');
const path = require('path');

function stripMarkdown(value) {
  return value.replace(/`([^`]+)`/g, '$1').replace(/[*_]([^*_]+)[*_]/g, '$1').trim();
}

function parseApiReference(markdown) {
  const functions = [];
  const sections = markdown.split(/^###\s+/m).slice(1);

  for (const section of sections) {
    const lines = section.split(/\r?\n/);
    const name = lines.shift().trim();
    const entry = { name, arguments: [] };
    let field = '';

    for (const line of lines) {
      let match;
      if ((match = line.match(/^- \*\*Obfuscated name:\*\*\s*(.+)$/))) {
        entry.obfuscatedName = stripMarkdown(match[1]);
        field = '';
      } else if ((match = line.match(/^- \*\*Availability:\*\*\s*(.+)$/))) {
        entry.availability = stripMarkdown(match[1]);
        field = '';
      } else if ((match = line.match(/^- \*\*Arguments:\*\*\s*(.*)$/))) {
        field = 'arguments';
        if (match[1].trim() === 'none') entry.arguments = [];
      } else if ((match = line.match(/^\s+- `([^`]+)` \(([^)]+)\)(?:\s+—\s+(.+))?$/)) && field === 'arguments') {
        const typeText = match[2];
        entry.arguments.push({
          name: match[1],
          type: typeText.replace(/,?\s*optional\b/i, '').trim(),
          optional: /\boptional\b/i.test(typeText),
          documentation: match[3] || ''
        });
      } else if ((match = line.match(/^- \*\*Returns:\*\*\s*(.+)$/))) {
        entry.returns = match[1];
        field = 'returns';
      } else if ((match = line.match(/^- \*\*Description:\*\*\s*(.*)$/))) {
        entry.description = match[1];
        field = 'description';
      } else if (field === 'description' && line.trim()) {
        entry.description += `\n\n${line.trim()}`;
      }
    }

    if (name) functions.push(entry);
  }
  return functions;
}

function signatureLabel(fn) {
  const args = fn.arguments.map(arg => `${arg.name}: ${arg.type}${arg.optional ? '?' : ''}`).join(', ');
  const returnType = fn.returns && fn.returns !== 'none' ? ` → ${stripMarkdown(fn.returns)}` : '';
  return `$${fn.name}(${args})${returnType}`;
}

function documentation(fn) {
  const value = new vscode.MarkdownString(undefined, true);
  value.appendMarkdown(`### \`$${fn.name}\`\n\n`);
  value.appendCodeblock(signatureLabel(fn), 'samurai-script');
  if (fn.description) value.appendMarkdown(`\n${fn.description}\n\n`);
  value.appendMarkdown(`**Availability:** ${fn.availability || 'unknown'}  \n`);
  value.appendMarkdown(`**Obfuscated name:** \`${fn.obfuscatedName || 'unknown'}\``);
  if (fn.returns) value.appendMarkdown(`  \n**Returns:** ${fn.returns}`);
  return value;
}

function activeArgument(document, position) {
  const text = document.getText(new vscode.Range(new vscode.Position(0, 0), position));
  const match = /\$([A-Za-z_]\w*)\s+([^$\n]*)$/.exec(text);
  if (!match) return undefined;
  let depth = 0;
  let commas = 0;
  let quote = '';
  for (const character of match[2]) {
    if (quote) {
      if (character === quote) quote = '';
    } else if (character === '"' || character === "'") quote = character;
    else if (character === '(' || character === '[') depth++;
    else if (character === ')' || character === ']') depth = Math.max(0, depth - 1);
    else if (character === ',' && depth === 0) commas++;
  }
  return { name: match[1], index: commas };
}

function activate(context) {
  const referencePath = path.join(context.extensionPath, 'api-reference.md');
  const functions = parseApiReference(fs.readFileSync(referencePath, 'utf8'));
  const byName = new Map(functions.map(fn => [fn.name.toLowerCase(), fn]));
  const selector = { language: 'samurai-script' };

  context.subscriptions.push(vscode.languages.registerCompletionItemProvider(selector, {
    provideCompletionItems(document, position) {
      const linePrefix = document.lineAt(position.line).text.slice(0, position.character);
      const functionPrefix = /\$[A-Za-z_]*$/.test(linePrefix) ? '' : '$';
      return functions.map(fn => {
        const item = new vscode.CompletionItem(fn.name, vscode.CompletionItemKind.Function);
        item.detail = signatureLabel(fn);
        item.documentation = documentation(fn);
        item.insertText = new vscode.SnippetString(fn.arguments.length
          ? `${functionPrefix}${fn.name} ${fn.arguments.map((arg, index) => `\${${index + 1}:${arg.name}}`).join(', ')}`
          : `${functionPrefix}${fn.name}`);
        item.command = fn.arguments.length
          ? { command: 'editor.action.triggerParameterHints', title: 'Trigger signature help' }
          : undefined;
        return item;
      });
    }
  }, '$'));

  context.subscriptions.push(vscode.languages.registerSignatureHelpProvider(selector, {
    provideSignatureHelp(document, position) {
      const call = activeArgument(document, position);
      const fn = call && byName.get(call.name.toLowerCase());
      if (!fn) return undefined;
      const signature = new vscode.SignatureInformation(signatureLabel(fn));
      signature.parameters = fn.arguments.map(arg =>
        new vscode.ParameterInformation(`${arg.name}: ${arg.type}${arg.optional ? '?' : ''}`, arg.documentation));
      const help = new vscode.SignatureHelp();
      help.signatures = [signature];
      help.activeSignature = 0;
      help.activeParameter = Math.min(call.index, Math.max(0, fn.arguments.length - 1));
      return help;
    }
  }, ',', ' '));

  context.subscriptions.push(vscode.languages.registerHoverProvider(selector, {
    provideHover(document, position) {
      const range = document.getWordRangeAtPosition(position, /\$?[A-Za-z_]\w*/);
      if (!range) return undefined;
      const name = document.getText(range).replace(/^\$/, '').toLowerCase();
      const fn = byName.get(name);
      return fn ? new vscode.Hover(documentation(fn), range) : undefined;
    }
  }));
}

module.exports = { activate, parseApiReference, activeArgument };
