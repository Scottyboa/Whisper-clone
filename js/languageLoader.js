// js/languageLoader.js

export async function loadLanguageModule(lang) {
  switch (lang) {
    case 'en':
      return import('./language/language-en.js');
    case 'no':
      return import('./language/language-no.js');
    case 'fr':
      return import('./language/language-fr.js');
    case 'de':
      return import('./language/language-de.js');
    case 'sv':
      return import('./language/language-sv.js');
    case 'it':
      return import('./language/language-it.js');
    default:
      return import('./language/language-en.js'); // fallback to English
  }
}
