// noteGeneration.js

// Utility function to hash a string (used for storing prompts keyed by API key)
function hashString(str) {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash |= 0; // Convert to 32bit integer
  }
  return hash.toString();
}

// Returns a storage key for a given prompt slot and API key
function getPromptStorageKey(slot) {
  const apiKey = sessionStorage.getItem("openai_api_key") || "";
  const hashedApiKey = hashString(apiKey);
  return "customPrompt_" + hashedApiKey + "_" + slot;
}

// Auto-resizes a textarea based on its content
function autoResize(textarea) {
  textarea.style.height = "auto";
  textarea.style.height = textarea.scrollHeight + "px";
}

// Loads the stored prompt for a given slot into the custom prompt textarea
function loadPromptForSlot(slot) {
  const key = getPromptStorageKey(slot);
  const storedPrompt = localStorage.getItem(key);
  const customPromptTextarea = document.getElementById("customPrompt");
  if (customPromptTextarea) {
    customPromptTextarea.value = storedPrompt ? storedPrompt : "";
    autoResize(customPromptTextarea);
  }
}

// Formats milliseconds into a human-readable string
function formatTime(ms) {
  const totalSec = Math.floor(ms / 1000);
  if (totalSec < 60) {
    return totalSec + " sec";
  } else {
    const minutes = Math.floor(totalSec / 60);
    const seconds = totalSec % 60;
    return minutes + " min" + (seconds > 0 ? " " + seconds + " sec" : "");
  }
}

// Handles the note generation process using the OpenAI API
async function generateNote() {
  const transcriptionElem = document.getElementById("transcription");
  if (!transcriptionElem) {
    alert("No transcription text available.");
    return;
  }
  const transcriptionText = transcriptionElem.value.trim();
  if (!transcriptionText) {
    alert("No transcription text available.");
    return;
  }
  
  const customPromptTextarea = document.getElementById("customPrompt");
  const promptText = customPromptTextarea ? customPromptTextarea.value : "";
  const generatedNoteField = document.getElementById("generatedNote");
  if (!generatedNoteField) return;
  
  // Reset generated note field and start timer
  generatedNoteField.value = "";
  const noteTimerElement = document.getElementById("noteTimer");
  const noteStartTime = Date.now();
  if (noteTimerElement) {
    noteTimerElement.innerText = "Note Generation Timer: 0 sec";
  }
  const noteTimerInterval = setInterval(() => {
    if (noteTimerElement) {
      noteTimerElement.innerText = "Note Generation Timer: " + formatTime(Date.now() - noteStartTime);
    }
  }, 1000);
  
  const apiKey = sessionStorage.getItem("openai_api_key");
  try {
    const response = await fetch("https://api.openai.com/v1/chat/completions", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": "Bearer " + apiKey
      },
      body: JSON.stringify({
        model: "gpt-4-turbo",
        messages: [
          { role: "system", content: promptText },
          { role: "user", content: transcriptionText }
        ],
        temperature: 0.7,
        stream: true
      })
    });
    const reader = response.body.getReader();
    const decoder = new TextDecoder("utf-8");
    let done = false;
    while (!done) {
      const { value, done: doneReading } = await reader.read();
      done = doneReading;
      const chunkValue = decoder.decode(value);
      const lines = chunkValue.split("\n").filter(line => line.trim() !== "");
      for (const line of lines) {
        if (line.startsWith("data: ")) {
          const jsonStr = line.replace("data: ", "").trim();
          if (jsonStr === "[DONE]") {
            done = true;
            break;
          }
          try {
            const parsed = JSON.parse(jsonStr);
            const textChunk = parsed.choices[0].delta?.content || "";
            generatedNoteField.value += textChunk;
            autoResize(generatedNoteField);
          } catch (err) {
            console.error("Stream chunk parsing error:", err);
          }
        }
      }
    }
    clearInterval(noteTimerInterval);
    if (noteTimerElement) {
      noteTimerElement.innerText = "Text generation completed!";
    }
  } catch (error) {
    clearInterval(noteTimerInterval);
    if (generatedNoteField) {
      generatedNoteField.value = "Error generating note: " + error;
    }
    if (noteTimerElement) {
      noteTimerElement.innerText = "";
    }
  }
}

// Initializes note generation functionality, including prompt slot handling and event listeners
function initNoteGeneration() {
  const promptSlotSelect = document.getElementById("promptSlot");
  const customPromptTextarea = document.getElementById("customPrompt");
  if (!promptSlotSelect || !customPromptTextarea) return;
  
  // Load the stored prompt for the current slot
  loadPromptForSlot(promptSlotSelect.value);
  
  // Save prompt changes on input
  customPromptTextarea.addEventListener("input", () => {
    const currentSlot = promptSlotSelect.value;
    const key = getPromptStorageKey(currentSlot);
    localStorage.setItem(key, customPromptTextarea.value);
    autoResize(customPromptTextarea);
  });
  
  // Load the prompt when the slot changes
  promptSlotSelect.addEventListener("change", () => {
    loadPromptForSlot(promptSlotSelect.value);
  });
  
  const generateNoteButton = document.getElementById("generateNoteButton");
  if (generateNoteButton) {
    generateNoteButton.addEventListener("click", generateNote);
  }
}

export { initNoteGeneration };
